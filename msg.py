import os
import sys
import smtplib
import imaplib
import email
import threading
import time
import json
import shutil
import socket
import select
import traceback
import base64
import re
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.mime.base import MIMEBase
from email import encoders
from email.utils import parsedate_to_datetime
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Set
from dataclasses import dataclass, asdict, field
import hashlib

from PyQt6.QtWidgets import *
from PyQt6.QtCore import *
from PyQt6.QtGui import *

from PyQt6.QtCore import QObject, pyqtSignal

CONFIG_FILE = "cfg.cfg"
DATA_DIR = Path("data")
CONTACTS_FILE = DATA_DIR / "contacts.json"
PROCESSED_UIDS_FILE = DATA_DIR / "processed_uids.json"

@dataclass
class Contact:
    email: str
    alias: str
    is_group: bool = False
    groupname: str = ""
    members: List[str] = field(default_factory=list)
    
    def __eq__(self, other):
        if not isinstance(other, Contact):
            return False
        if self.is_group and other.is_group:
            return self.groupname == other.groupname
        elif not self.is_group and not other.is_group:
            return self.email.lower() == other.email.lower()
        return False
    
    def __hash__(self):
        if self.is_group:
            return hash(f"group_{self.groupname}")
        return hash(f"contact_{self.email.lower()}")

class Config:
    def __init__(self):
        self.smtp_server = self.smtp_port = None
        self.imap_server = self.imap_port = None
        self.imap_ssl = True
        self.imap_idle = True
        self.imap_keepalive = 20
        self.email = self.password = ""
        self.messenger_subject_prefix = "bd6d6648f39621d16d0548f1a7c582ea"
        self.poll_interval = 30
        self.imap_folder = None
        self.load()
    
    def load(self):
        if not os.path.exists(CONFIG_FILE):
            return
        with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                if '=' not in line:
                    continue
                key, val = line.split('=', 1)
                key = key.strip()
                val = val.strip()
                if '#' in val:
                    val = val.split('#')[0].strip()
                val = val.strip(' "')
                try:
                    if key == "SMTP_SERVER":
                        self.smtp_server = val
                    elif key == "SMTP_PORT":
                        self.smtp_port = int(val)
                    elif key == "IMAP_SERVER":
                        self.imap_server = val
                    elif key == "IMAP_PORT":
                        self.imap_port = int(val)
                    elif key == "IMAP_SSL":
                        self.imap_ssl = val.lower() == 'true'
                    elif key == "IMAP_IDLE":
                        self.imap_idle = val.lower() == 'true'
                    elif key == "IMAP_KEEPALIVE":
                        self.imap_keepalive = int(val)
                    elif key == "EMAIL":
                        self.email = val
                    elif key == "PASSWORD":
                        self.password = val
                    elif key == "MESSENGER_SUBJECT_PREFIX":
                        self.messenger_subject_prefix = val
                    elif key == "POLL_INTERVAL":
                        self.poll_interval = int(val)
                    elif key == "IMAP_FOLDER":
                        self.imap_folder = val
                except ValueError as e:
                    print(f"Ошибка парсинга {key}={val}: {e}")

class MessageLogger:
    def __init__(self, contact: Contact):
        self.contact = contact
        self.dir = DATA_DIR / (contact.groupname if contact.is_group else contact.email)
        self.log_file = self.dir / "log.txt"
        self.last_time_file = self.dir / "last_time.txt"
        self.attachments_dir = self.dir / "attachments"
        self.dir.mkdir(parents=True, exist_ok=True)
        self.attachments_dir.mkdir(exist_ok=True)
    
    def get_last_time(self) -> Optional[float]:
        if self.last_time_file.exists():
            try:
                with open(self.last_time_file, 'r') as f:
                    return float(f.read().strip())
            except:
                pass
        return None
    
    def add_message(self, text: str, is_outgoing: bool, attachments: List[str], 
                    msg_time: float, sender: str, uid: str = None):
        last = self.get_last_time()
        if last and msg_time <= last:
            return False
        
        timestamp = datetime.fromtimestamp(msg_time).strftime("%Y-%m-%d %H:%M:%S")
        direction = "→" if is_outgoing else "←"
        
        with open(self.log_file, 'a', encoding='utf-8') as f:
            f.write(f"[{timestamp}] {sender} {direction} {text}\n")
            if attachments:
                f.write(f"Вложения: {', '.join(attachments)}\n")
            if uid:
                f.write(f"UID: {uid}\n")
        
        with open(self.last_time_file, 'w') as f:
            f.write(str(msg_time))
        return True
    
    def save_attachment(self, data: bytes, filename: str):
        filepath = self.attachments_dir / filename
        with open(filepath, 'wb') as f:
            f.write(data)
        return str(filepath)

class EmailClient(QObject):
    message_received = pyqtSignal(object, str, bool, list, float, str, list)
    initial_scan_completed = pyqtSignal()
    
    def __init__(self, config):
        super().__init__()
        self.config = config
        self.running = True
        self.processed_uids: Dict[str, Set[str]] = {}
        self.main_window = None
        self.idle_thread = None
        self.tag_counter = 0
        self.target_folder = config.imap_folder
        self.last_scan_time_file = Path("data/last_scan_time.txt")
        self.last_scan_time = self._load_last_scan_time()
        self._load_processed()
    
    def _load_last_scan_time(self) -> float:
        if self.last_scan_time_file.exists():
            try:
                with open(self.last_scan_time_file, 'r') as f:
                    return float(f.read().strip())
            except:
                pass
        return 0
    
    def _save_last_scan_time(self):
        try:
            with open(self.last_scan_time_file, 'w') as f:
                f.write(str(time.time()))
        except:
            pass
    
    def _load_processed(self):
        processed_file = Path("data/processed_uids.json")
        if processed_file.exists():
            try:
                with open(processed_file, 'r') as f:
                    data = json.load(f)
                    self.processed_uids = {k: set(v) for k, v in data.items()}
            except:
                pass
    
    def _save_processed(self):
        data = {k: list(v) for k, v in self.processed_uids.items()}
        with open(Path("data/processed_uids.json"), 'w') as f:
            json.dump(data, f)
    
    def set_main_window(self, window):
        self.main_window = window
    
    def start(self):
        threading.Thread(target=self._initial_scan, daemon=True).start()
    
    def stop(self):
        self.running = False
        if self.idle_thread:
            self.idle_thread.join(timeout=2)
    
    def _get_tag(self) -> bytes:
        self.tag_counter += 1
        return f"A{self.tag_counter:03d}".encode()
    
    def _connect(self):
        try:
            if self.config.imap_ssl:
                mail = imaplib.IMAP4_SSL(self.config.imap_server, self.config.imap_port)
            else:
                mail = imaplib.IMAP4(self.config.imap_server, self.config.imap_port)
            mail.login(self.config.email, self.config.password)
            return mail
        except Exception as e:
            print(f"IMAP connection error: {e}")
            return None
    
    def _quote_folder(self, folder: str) -> str:
        if ' ' in folder or '"' in folder:
            return f'"{folder}"'
        return folder
    
    def _initial_scan(self):
        print("\n=== НАЧАЛО ПЕРВИЧНОГО СКАНИРОВАНИЯ ===")
        
        if not self.target_folder:
            print("ОШИБКА: IMAP_FOLDER не указана в cfg.cfg")
            self.initial_scan_completed.emit()
            return
        
        mail = self._connect()
        if not mail:
            print("ОШИБКА: не удалось подключиться к IMAP серверу")
            self.initial_scan_completed.emit()
            return
        
        try:
            quoted = self._quote_folder(self.target_folder)
            result = mail.select(quoted)
            if result[0] != 'OK':
                print(f"ОШИБКА: папка '{self.target_folder}' не найдена или недоступна")
                mail.logout()
                self.initial_scan_completed.emit()
                return
            print(f"✓ Целевая папка '{self.target_folder}' успешно выбрана")
        except Exception as e:
            print(f"ОШИБКА при выборе папки: {e}")
            mail.logout()
            self.initial_scan_completed.emit()
            return
        
        self._scan_folder_since_time(mail, self.target_folder, self.last_scan_time)
        
        self.last_scan_time = time.time()
        self._save_last_scan_time()
        
        mail.logout()
        
        self.initial_scan_completed.emit()
        
        self._start_idle_monitor_for_folder(self.target_folder)
    
    def _scan_folder_since_time(self, mail, folder, since_time):
        try:
            quoted = self._quote_folder(folder)
            result = mail.select(quoted)
            if result[0] != 'OK':
                return
            
            since_date = datetime.fromtimestamp(since_time).strftime("%d-%b-%Y")
            result, uids = mail.uid('search', None, f'SINCE "{since_date}"')
            if result != 'OK' or not uids[0]:
                return
            
            messages = []
            for uid in uids[0].split():
                uid_str = uid.decode() if isinstance(uid, bytes) else str(uid)
                result, data = mail.uid('fetch', uid, '(BODY.PEEK[HEADER.FIELDS (SUBJECT)])')
                if result == 'OK' and data[0]:
                    header = data[0][1]
                    if isinstance(header, bytes):
                        header_str = header.decode('utf-8', errors='ignore')
                        m = re.search(r'Subject:\s*(.+)', header_str, re.IGNORECASE)
                        if m:
                            subj = m.group(1).strip()
                            if subj.startswith(self.config.messenger_subject_prefix):
                                messages.append((uid, subj))
            
            if not messages:
                return
            
            processed = self.processed_uids.get(folder, set())
            new_msgs = []
            for uid, subj in messages:
                uid_str = uid.decode() if isinstance(uid, bytes) else str(uid)
                if uid_str not in processed:
                    new_msgs.append((uid, subj))
            
            if new_msgs:
                print(f"  {folder}: {len(new_msgs)} оффлайн-сообщений")
                for uid, subj in new_msgs:
                    uid_str = uid.decode() if isinstance(uid, bytes) else str(uid)
                    self._fetch_message(mail, uid_str, folder, subj)
                    processed.add(uid_str)
                self.processed_uids[folder] = processed
                self._save_processed()
                
        except Exception as e:
            print(f"Ошибка сканирования {folder}: {e}")
    
    def _scan_for_unseen_messages(self, mail, folder):
        try:
            quoted = self._quote_folder(folder)
            result = mail.select(quoted)
            if result[0] != 'OK':
                return
            
            result, uids = mail.uid('search', None, 'UNSEEN')
            if result != 'OK' or not uids[0]:
                return
            
            messages = []
            for uid in uids[0].split():
                uid_str = uid.decode() if isinstance(uid, bytes) else str(uid)
                result, data = mail.uid('fetch', uid, '(BODY.PEEK[HEADER.FIELDS (SUBJECT)])')
                if result == 'OK' and data[0]:
                    header = data[0][1]
                    if isinstance(header, bytes):
                        header_str = header.decode('utf-8', errors='ignore')
                        m = re.search(r'Subject:\s*(.+)', header_str, re.IGNORECASE)
                        if m:
                            subj = m.group(1).strip()
                            if subj.startswith(self.config.messenger_subject_prefix):
                                messages.append((uid, subj))
            
            if not messages:
                return
            
            processed = self.processed_uids.get(folder, set())
            new_msgs = []
            for uid, subj in messages:
                uid_str = uid.decode() if isinstance(uid, bytes) else str(uid)
                if uid_str not in processed:
                    new_msgs.append((uid, subj))
            
            if new_msgs:
                print(f"  {folder}: {len(new_msgs)} новых сообщений")
                for uid, subj in new_msgs:
                    uid_str = uid.decode() if isinstance(uid, bytes) else str(uid)
                    self._fetch_message(mail, uid_str, folder, subj)
                    processed.add(uid_str)
                self.processed_uids[folder] = processed
                self._save_processed()
                
        except Exception as e:
            print(f"Ошибка сканирования {folder}: {e}")
    
    def _start_idle_monitor_for_folder(self, folder):
        self.idle_folder = folder
        self.idle_thread = threading.Thread(target=self._idle_loop_for_folder, daemon=True)
        self.idle_thread.start()
        print(f"IDLE запущен для папки '{folder}'")
    
    def _idle_loop_for_folder(self):
        while self.running:
            mail = None
            try:
                mail = self._connect()
                if not mail:
                    time.sleep(10)
                    continue
                
                quoted = self._quote_folder(self.idle_folder)
                result = mail.select(quoted)
                if result[0] != 'OK':
                    print(f"Не могу выбрать {self.idle_folder}")
                    mail.logout()
                    time.sleep(30)
                    continue
                
                test_tag = self._get_tag()
                mail.sock.send(test_tag + b' IDLE\r\n')
                test_resp = mail.sock.recv(1024)
                if b'BAD' in test_resp or b'NO' in test_resp:
                    mail.sock.send(b'DONE\r\n')
                    mail.logout()
                    time.sleep(30)
                    continue
                mail.sock.send(b'DONE\r\n')
                mail.sock.recv(1024)
                time.sleep(1)
                
                tag = self._get_tag()
                mail.sock.send(tag + b' IDLE\r\n')
                resp = mail.sock.recv(1024)
                if b'+' in resp:
                    idle_active = True
                    while self.running and idle_active:
                        try:
                            ready = select.select([mail.sock], [], [], 60)
                            if ready[0]:
                                data = mail.sock.recv(1024)
                                if b'EXISTS' in data or b'RECENT' in data:
                                    print("IDLE: новое сообщение!")
                                    mail.sock.send(b'DONE\r\n')
                                    mail.sock.recv(1024)
                                    self._scan_for_unseen_messages(mail, self.idle_folder)
                                    self.last_scan_time = time.time()
                                    self._save_last_scan_time()
                                    idle_active = False
                                    break
                                elif b'BYE' in data:
                                    print("Сервер завершил соединение")
                                    idle_active = False
                                    break
                            else:
                                mail.sock.send(b'DONE\r\n')
                                mail.sock.recv(1024)
                                mail.noop()
                                time.sleep(0.1)
                                new_tag = self._get_tag()
                                mail.sock.send(new_tag + b' IDLE\r\n')
                                idle_resp = mail.sock.recv(1024)
                                if not (b'+' in idle_resp):
                                    print("Не удалось перезапустить IDLE")
                                    idle_active = False
                                    break
                        except socket.timeout:
                            continue
                        except Exception as e:
                            print(f"IDLE error: {e}")
                            idle_active = False
                            break
                mail.logout()
            except Exception as e:
                print(f"IDLE loop error: {e}")
                if mail:
                    try:
                        mail.logout()
                    except:
                        pass
                time.sleep(10)
    
    def _fetch_message(self, mail, uid, folder, subject):
        if not subject.startswith(self.config.messenger_subject_prefix):
            return
        result, data = mail.uid('fetch', uid, '(RFC822)')
        if result != 'OK' or not data or not data[0]:
            return
        msg = email.message_from_bytes(data[0][1])
        from_addr = email.utils.parseaddr(msg.get("From"))[1]
        if from_addr.lower() == self.config.email.lower():
            return
        groupname = subject[len(self.config.messenger_subject_prefix):]
        msg_time = self._get_msg_time(msg)
        text, attachments, attachment_paths = self._extract_message_content(msg, folder)
        to_header = msg.get("To", "")
        to_addrs = []
        if to_header:
            for x in to_header.split(","):
                addr = email.utils.parseaddr(x)[1]
                if addr and addr != self.config.email:
                    to_addrs.append(addr.lower())
        self._process_message(text, attachments, attachment_paths, msg_time, from_addr.lower(),
                              to_addrs, groupname, uid)
        mail.uid('STORE', uid, '+FLAGS', '\\Seen')
    
    def _extract_message_content(self, msg, folder):
        text = ""
        attachments = []
        attachment_paths = []
        
        if msg.is_multipart():
            for part in msg.walk():
                ct = part.get_content_type()
                cd = str(part.get("Content-Disposition"))
                if ct == "text/plain" and "attachment" not in cd:
                    try:
                        payload = part.get_payload(decode=True)
                        text = payload.decode('utf-8', errors='ignore')
                    except:
                        pass
                elif "attachment" in cd:
                    filename = part.get_filename()
                    if filename:
                        attachments.append(filename)
                        data = part.get_payload(decode=True)
                        # Сохраняем вложение во временное место
                        temp_dir = Path("temp_attachments")
                        temp_dir.mkdir(exist_ok=True)
                        temp_path = temp_dir / filename
                        with open(temp_path, 'wb') as f:
                            f.write(data)
                        attachment_paths.append(str(temp_path))
        else:
            try:
                text = msg.get_payload(decode=True).decode('utf-8', errors='ignore')
            except:
                pass
        return text, attachments, attachment_paths
    
    def _get_msg_time(self, msg):
        try:
            return parsedate_to_datetime(msg.get("Date", "")).timestamp()
        except:
            return time.time()
    
    def _process_message(self, text, attachments, attachment_paths, msg_time, from_addr, to_addrs, groupname, uid):
        contacts = self._load_contacts()
        if groupname:
            contact = None
            for c in contacts:
                if c.is_group and c.groupname == groupname:
                    contact = c
                    break
            if not contact:
                all_members = list(dict.fromkeys([from_addr] + to_addrs))
                contact = Contact(email="", alias=groupname[:10], is_group=True,
                                  groupname=groupname, members=all_members)
                contacts.append(contact)
                for member in all_members:
                    self._save_group_alias(groupname, member, member.split('@')[0])
            aliases = self._load_group_aliases(groupname)
            sender_alias = aliases.get(from_addr, from_addr.split('@')[0])
            if from_addr not in [m.lower() for m in contact.members]:
                contact.members.append(from_addr)
            self._save_contacts(contacts)
            if self.main_window:
                self.main_window._add_contact_to_list(contact)
            logger = MessageLogger(contact)
            
            # Сохраняем вложения
            saved_paths = []
            for i, path in enumerate(attachment_paths):
                filename = attachments[i] if i < len(attachments) else f"attachment_{i}"
                saved_path = logger.save_attachment(open(path, 'rb').read(), filename)
                saved_paths.append(saved_path)
                os.remove(path)  # Удаляем временный файл
            
            logger.add_message(text, False, attachments, msg_time, sender_alias, uid)
            self.message_received.emit(contact, text, False, attachments, msg_time, sender_alias, saved_paths)
        else:
            contact = None
            for c in contacts:
                if not c.is_group and c.email.lower() == from_addr:
                    contact = c
                    break
            if not contact:
                sender_alias = from_addr.split('@')[0]
                contact = Contact(email=from_addr, alias=sender_alias)
                contacts.append(contact)
                self._save_contacts(contacts)
                if self.main_window:
                    self.main_window._add_contact_to_list(contact)
            else:
                sender_alias = contact.alias
            logger = MessageLogger(contact)
            
            # Сохраняем вложения
            saved_paths = []
            for i, path in enumerate(attachment_paths):
                filename = attachments[i] if i < len(attachments) else f"attachment_{i}"
                saved_path = logger.save_attachment(open(path, 'rb').read(), filename)
                saved_paths.append(saved_path)
                os.remove(path)  # Удаляем временный файл
            
            logger.add_message(text, False, attachments, msg_time, sender_alias, uid)
            self.message_received.emit(contact, text, False, attachments, msg_time, sender_alias, saved_paths)
    
    def _load_group_aliases(self, groupname):
        file = Path("data") / f"group_{groupname}_aliases.json"
        if file.exists():
            try:
                with open(file, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except:
                pass
        return {}
    
    def _save_group_alias(self, groupname, email, alias):
        file = Path("data") / f"group_{groupname}_aliases.json"
        aliases = self._load_group_aliases(groupname)
        aliases[email] = alias
        with open(file, 'w', encoding='utf-8') as f:
            json.dump(aliases, f, ensure_ascii=False, indent=2)
    
    def _load_contacts(self):
        file = Path("data/contacts.json")
        if file.exists():
            try:
                with open(file, 'r', encoding='utf-8') as f:
                    return [Contact(**c) for c in json.load(f)]
            except:
                pass
        return []
    
    def _save_contacts(self, contacts):
        with open(Path("data/contacts.json"), 'w', encoding='utf-8') as f:
            json.dump([asdict(c) for c in contacts], f, ensure_ascii=False, indent=2)
    
    def send_message(self, contact, text, attachments):
        if not self.config.smtp_server:
            return False
        recipients = contact.members if contact.is_group else [contact.email]
        recipients = [r for r in recipients if r.lower() != self.config.email.lower()]
        if not recipients:
            return False
        msg = MIMEMultipart()
        msg["From"] = self.config.email
        msg["To"] = ", ".join(recipients)
        if contact.is_group:
            msg["Subject"] = f"{self.config.messenger_subject_prefix}{contact.groupname}"
        else:
            msg["Subject"] = self.config.messenger_subject_prefix
        msg.attach(MIMEText(text, "plain"))
        for path in attachments:
            try:
                with open(path, "rb") as f:
                    part = MIMEBase("application", "octet-stream")
                    part.set_payload(f.read())
                    encoders.encode_base64(part)
                    part.add_header("Content-Disposition", f"attachment; filename={os.path.basename(path)}")
                    msg.attach(part)
            except:
                pass
        try:
            server = smtplib.SMTP(self.config.smtp_server, self.config.smtp_port)
            if self.config.password:
                server.login(self.config.email, self.config.password)
            server.send_message(msg)
            server.quit()
            logger = MessageLogger(contact)
            logger.add_message(text, True, attachments, time.time(), "Я", None)
            return True
        except Exception as e:
            print(f"Ошибка отправки: {e}")
            return False

class ChatTitleBar(QWidget):
    def __init__(self, title="", parent=None):
        super().__init__(parent)
        layout = QHBoxLayout()
        layout.setContentsMargins(10, 5, 10, 5)
        self.title_label = QLabel(title)
        self.title_label.setStyleSheet("font-weight: bold; font-size: 14px;")
        layout.addWidget(self.title_label)
        layout.addStretch()
        self.setLayout(layout)
        self.setStyleSheet("background-color: #f0f0f0; border-bottom: 1px solid #ccc;")
    
    def set_title(self, title):
        self.title_label.setText(title)

class SplitterWithHandle(QSplitter):
    def __init__(self, orientation, parent=None):
        super().__init__(orientation, parent)
        self.setHandleWidth(4)
        self.setStyleSheet("""
            QSplitter::handle {
                background-color: #ccc;
            }
            QSplitter::handle:hover {
                background-color: #999;
            }
        """)

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.config = Config()
        self.contacts = self._load_contacts()
        self.current_contact = None
        self.attachments = []
        self.last_view = {}
        self.unread_counts = {}
        
        self.client = EmailClient(self.config)
        self.client.set_main_window(self)
        self.client.message_received.connect(self._on_message)
        self.client.initial_scan_completed.connect(self._on_scan_done)
        
        self._init_ui()
        self._refresh_list()
        self.client.start()
        self.statusBar().showMessage("Выполняется начальное сканирование...")
    
    def _load_contacts(self):
        if CONTACTS_FILE.exists():
            try:
                with open(CONTACTS_FILE, 'r', encoding='utf-8') as f:
                    return [Contact(**c) for c in json.load(f)]
            except:
                pass
        return []
    
    def _save_contacts(self):
        with open(CONTACTS_FILE, 'w', encoding='utf-8') as f:
            json.dump([asdict(c) for c in self.contacts], f, ensure_ascii=False, indent=2)
    
    def _init_ui(self):
        self.setWindowTitle("Почтовый мессенджер")
        self.setGeometry(100, 100, 1200, 600)
        
        central = QWidget()
        self.setCentralWidget(central)
        layout = QHBoxLayout(central)
        
        # Левая панель
        left = QWidget()
        left.setMaximumWidth(300)
        left_layout = QVBoxLayout(left)
        
        self.list = QListWidget()
        self.list.itemClicked.connect(self._select_contact)
        self.list.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.list.customContextMenuRequested.connect(self._context_menu)
        
        btn_add = QPushButton("➕ Добавить контакт")
        btn_add.clicked.connect(self._add_contact)
        btn_group = QPushButton("👥 Добавить группу")
        btn_group.clicked.connect(self._add_group)
        
        left_layout.addWidget(QLabel("Контакты:"))
        left_layout.addWidget(self.list)
        left_layout.addWidget(btn_add)
        left_layout.addWidget(btn_group)
        
        # Правая панель
        right = QWidget()
        right_layout = QVBoxLayout(right)
        right_layout.setContentsMargins(0, 0, 0, 0)
        
        # Заголовок чата
        self.chat_title = ChatTitleBar("Не выбран чат")
        right_layout.addWidget(self.chat_title)
        
        # Создаем сплиттер для области чата и ввода
        self.chat_splitter = SplitterWithHandle(Qt.Orientation.Vertical)
        
        # Окно чата
        self.chat = QTextEdit()
        self.chat.setReadOnly(True)
        self.chat.setStyleSheet("QTextEdit { font-family: monospace; font-size: 12px; }")
        self.chat_splitter.addWidget(self.chat)
        
        # Область ввода сообщения
        input_container = QWidget()
        input_layout = QVBoxLayout(input_container)
        
        # Отображение вложений
        self.attachments_label = QLabel()
        self.attachments_label.setVisible(False)
        self.attachments_label.setStyleSheet("background-color: #e0e0e0; padding: 5px; border-radius: 3px;")
        
        self.input = QTextEdit()
        self.input.setMaximumHeight(100)
        self.input.setPlaceholderText("Введите сообщение... (Enter - отправка)")
        self.input.installEventFilter(self)
        
        btn_send = QPushButton("Отправить")
        btn_send.clicked.connect(self._send)
        btn_attach = QPushButton("📎 Вложение")
        btn_attach.clicked.connect(self._attach)
        btn_clear_attach = QPushButton("🗑 Очистить вложения")
        btn_clear_attach.clicked.connect(self._clear_attachments)
        
        btn_layout = QHBoxLayout()
        btn_layout.addWidget(btn_send)
        btn_layout.addWidget(btn_attach)
        btn_layout.addWidget(btn_clear_attach)
        
        input_layout.addWidget(self.attachments_label)
        input_layout.addWidget(self.input)
        input_layout.addLayout(btn_layout)
        
        self.chat_splitter.addWidget(input_container)
        
        # Устанавливаем начальные пропорции (70% чат, 30% ввод)
        self.chat_splitter.setSizes([400, 200])
        
        right_layout.addWidget(self.chat_splitter)
        
        layout.addWidget(left)
        layout.addWidget(right, stretch=1)
    
    def eventFilter(self, obj, event):
        if obj == self.input and event.type() == QEvent.Type.KeyPress:
            if event.key() == Qt.Key.Key_Return and not (event.modifiers() & Qt.KeyboardModifier.ShiftModifier):
                self._send()
                return True
        return super().eventFilter(obj, event)
    
    def _refresh_list(self):
        self.list.clear()
        for c in self.contacts:
            icon = "👥" if c.is_group else "👤"
            key = c.groupname if c.is_group else c.email.lower()
            unread = self.unread_counts.get(key, 0)
            
            text = f"{icon} {c.alias}"
            if c.is_group:
                text += f" ({len(c.members)} уч.)"
            if unread > 0:
                text += f" ({unread})"
                item = QListWidgetItem(text)
                font = item.font()
                font.setBold(True)
                item.setFont(font)
            else:
                item = QListWidgetItem(text)
            
            item.setData(Qt.ItemDataRole.UserRole, c)
            self.list.addItem(item)
    
    def _has_unread(self, contact):
        last_msg = MessageLogger(contact).get_last_time()
        if last_msg:
            key = contact.groupname if contact.is_group else contact.email.lower()
            return last_msg > self.last_view.get(key, 0)
        return False
    
    def _update_unread_count(self, contact, force_update=False):
        """Обновляет счетчик непрочитанных сообщений для контакта"""
        key = contact.groupname if contact.is_group else contact.email.lower()
        last_view = self.last_view.get(key, 0)
        logger = MessageLogger(contact)
        
        if logger.log_file.exists():
            try:
                with open(logger.log_file, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                # Считаем сообщения после last_view
                count = 0
                for line in lines:
                    if '←' in line:  # Входящие сообщения
                        # Извлекаем время из строки [2024-01-01 12:00:00]
                        match = re.search(r'\[(.*?)\]', line)
                        if match:
                            try:
                                msg_time = datetime.strptime(match.group(1), "%Y-%m-%d %H:%M:%S").timestamp()
                                if msg_time > last_view:
                                    count += 1
                            except:
                                pass
                self.unread_counts[key] = count
            except:
                pass
    
    def _mark_as_read(self, contact):
        """Отмечает все сообщения контакта как прочитанные"""
        key = contact.groupname if contact.is_group else contact.email.lower()
        self.last_view[key] = time.time()
        self.unread_counts[key] = 0
        self._refresh_list()
    
    def _select_contact(self, item):
        self.current_contact = item.data(Qt.ItemDataRole.UserRole)
        
        # Обновляем заголовок
        if self.current_contact.is_group:
            self.chat_title.set_title(f"Чат группы: {self.current_contact.alias} ({len(self.current_contact.members)} уч.)")
        else:
            self.chat_title.set_title(f"Чат с: {self.current_contact.alias}")
        
        self._load_history()
        self._mark_as_read(self.current_contact)
        
        # Прокручиваем вниз
        self.chat.verticalScrollBar().setValue(self.chat.verticalScrollBar().maximum())
    
    def _load_history(self):
        self.chat.clear()
        logger = MessageLogger(self.current_contact)
        if logger.log_file.exists():
            try:
                with open(logger.log_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                    self.chat.setText(content)
            except:
                pass
    
    def _add_contact(self):
        dialog = QDialog(self)
        dialog.setWindowTitle("Новый контакт")
        layout = QFormLayout(dialog)
        
        alias = QLineEdit()
        email = QLineEdit()
        layout.addRow("Алиас:", alias)
        layout.addRow("Email:", email)
        
        btn = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        layout.addWidget(btn)
        
        def accept():
            if alias.text() and email.text():
                self.contacts.append(Contact(email=email.text().lower(), alias=alias.text()))
                self._save_contacts()
                self._refresh_list()
                dialog.accept()
        
        btn.accepted.connect(accept)
        btn.rejected.connect(dialog.reject)
        dialog.exec()
    
    def _add_contact_to_list(self, contact):
        for i in range(self.list.count()):
            item = self.list.item(i)
            existing = item.data(Qt.ItemDataRole.UserRole)
            if existing.is_group and contact.is_group:
                if existing.groupname == contact.groupname:
                    return
            elif not existing.is_group and not contact.is_group:
                if existing.email.lower() == contact.email.lower():
                    return
        
        icon = "👥" if contact.is_group else "👤"
        text = f"{icon} {contact.alias}"
        if contact.is_group:
            text += f" ({len(contact.members)} уч.)"
        
        item = QListWidgetItem(text)
        item.setData(Qt.ItemDataRole.UserRole, contact)
        self.list.addItem(item)
        
        found = False
        for c in self.contacts:
            if c.is_group and contact.is_group:
                if c.groupname == contact.groupname:
                    found = True
                    break
            elif not c.is_group and not contact.is_group:
                if c.email.lower() == contact.email.lower():
                    found = True
                    break
        
        if not found:
            self.contacts.append(contact)
            self._save_contacts()
    
    def _add_group(self):
        dialog = QDialog(self)
        dialog.setWindowTitle("Создание группы")
        layout = QVBoxLayout(dialog)
        
        layout.addWidget(QLabel("Название группы:"))
        name = QLineEdit()
        layout.addWidget(name)
        
        layout.addWidget(QLabel("Участники (email через запятую):"))
        members = QTextEdit()
        members.setMaximumHeight(100)
        layout.addWidget(members)
        
        btn = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        layout.addWidget(btn)
        
        def accept():
            if name.text() and members.toPlainText().strip():
                emails = [e.strip().lower() for e in members.toPlainText().split(',') if e.strip()]
                groupname = hashlib.md5(str(time.time()).encode()).hexdigest()[:16]
                group = Contact(email="", alias=name.text(), is_group=True, groupname=groupname, members=emails)
                self.contacts.append(group)
                self._save_contacts()
                
                for email in emails:
                    self._save_group_alias(groupname, email, email.split('@')[0])
                
                self._refresh_list()
                dialog.accept()
        
        btn.accepted.connect(accept)
        btn.rejected.connect(dialog.reject)
        dialog.exec()
    
    def _save_group_alias(self, groupname, email, alias):
        file = DATA_DIR / f"group_{groupname}_aliases.json"
        aliases = self._load_group_aliases(groupname)
        aliases[email.lower()] = alias
        with open(file, 'w', encoding='utf-8') as f:
            json.dump(aliases, f, ensure_ascii=False, indent=2)
    
    def _load_group_aliases(self, groupname):
        file = DATA_DIR / f"group_{groupname}_aliases.json"
        if file.exists():
            try:
                with open(file, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except:
                pass
        return {}

    def _show_group_members(self, group):
        dialog = QDialog(self)
        dialog.setWindowTitle(f"Участники: {group.alias}")
        dialog.setMinimumWidth(500)
        dialog.setMinimumHeight(400)
        
        layout = QVBoxLayout(dialog)
        layout.addWidget(QLabel(f"Всего: {len(group.members)}"))
        
        table = QTableWidget()
        table.setColumnCount(2)
        table.setHorizontalHeaderLabels(["Алиас", "Email"])
        table.horizontalHeader().setStretchLastSection(True)
        
        aliases = self._load_group_aliases(group.groupname)
        
        table.setRowCount(len(group.members))
        for i, email in enumerate(group.members):
            alias = aliases.get(email.lower(), email.split('@')[0])
            alias_item = QTableWidgetItem(alias)
            alias_item.setFlags(alias_item.flags() | Qt.ItemFlag.ItemIsEditable)
            email_item = QTableWidgetItem(email)
            email_item.setFlags(email_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
            table.setItem(i, 0, alias_item)
            table.setItem(i, 1, email_item)
        
        def on_alias_changed(row, col):
            # Добавляем проверку, что ячейки существуют
            if col == 0:
                email_item = table.item(row, 1)
                alias_item = table.item(row, 0)
                
                # Проверяем, что оба элемента существуют
                if email_item is not None and alias_item is not None:
                    email = email_item.text()
                    new_alias = alias_item.text()
                    if new_alias.strip():
                        self._save_group_alias(group.groupname, email, new_alias)
                        self._refresh_list()
        
        def on_double_click(row, col):
            if col == 1:
                email_item = table.item(row, 1)
                if email_item is not None:
                    email = email_item.text().lower()
                    aliases = self._load_group_aliases(group.groupname)
                    alias = aliases.get(email, email.split('@')[0])
                    
                    contact = None
                    for c in self.contacts:
                        if not c.is_group and c.email.lower() == email:
                            contact = c
                            break
                    
                    if not contact:
                        contact = Contact(email=email, alias=alias)
                        self.contacts.append(contact)
                        self._save_contacts()
                        self._refresh_list()
                    
                    self._select_contact_by_email(email)
                    dialog.accept()
        
        # Отключаем сигнал временно при заполнении таблицы
        table.blockSignals(True)
        table.cellChanged.connect(on_alias_changed)
        table.cellDoubleClicked.connect(on_double_click)
        table.blockSignals(False)
        layout.addWidget(table)
        
        btn_layout = QHBoxLayout()
        btn_add = QPushButton("➕ Добавить")
        btn_remove = QPushButton("❌ Удалить")
        btn_close = QPushButton("Закрыть")
        btn_layout.addWidget(btn_add)
        btn_layout.addWidget(btn_remove)
        btn_layout.addStretch()
        btn_layout.addWidget(btn_close)
        layout.addLayout(btn_layout)
        
        def on_add():
            add_dialog = QDialog(dialog)
            add_dialog.setWindowTitle("Добавить участника")
            add_layout = QFormLayout(add_dialog)
            
            alias_edit = QLineEdit()
            email_edit = QLineEdit()
            add_layout.addRow("Алиас:", alias_edit)
            add_layout.addRow("Email:", email_edit)
            
            btn_ok = QPushButton("Добавить")
            btn_cancel = QPushButton("Отмена")
            btn_hlayout = QHBoxLayout()
            btn_hlayout.addWidget(btn_ok)
            btn_hlayout.addWidget(btn_cancel)
            add_layout.addRow(btn_hlayout)
            
            def do_add():
                alias = alias_edit.text().strip()
                email = email_edit.text().strip().lower()
                if alias and email:
                    if email not in [m.lower() for m in group.members]:
                        # Добавляем участника
                        group.members.append(email)
                        self._save_group_alias(group.groupname, email, alias)
                        self._save_contacts()
                        
                        # Блокируем сигналы при добавлении строки
                        table.blockSignals(True)
                        row = table.rowCount()
                        table.insertRow(row)
                        
                        # Создаем элементы
                        alias_item = QTableWidgetItem(alias)
                        alias_item.setFlags(alias_item.flags() | Qt.ItemFlag.ItemIsEditable)
                        email_item = QTableWidgetItem(email)
                        email_item.setFlags(email_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
                        
                        table.setItem(row, 0, alias_item)
                        table.setItem(row, 1, email_item)
                        table.blockSignals(False)
                        
                        # Обновляем счетчик участников
                        layout.itemAt(0).widget().setText(f"Всего: {len(group.members)}")
                        self._refresh_list()
                        add_dialog.accept()
                    else:
                        QMessageBox.warning(add_dialog, "Ошибка", "Участник уже есть в группе")
            
            btn_ok.clicked.connect(do_add)
            btn_cancel.clicked.connect(add_dialog.reject)
            add_dialog.exec()
        
        def on_remove():
            current_row = table.currentRow()
            if current_row >= 0:
                email_item = table.item(current_row, 1)
                if email_item is not None:
                    email = email_item.text()
                    reply = QMessageBox.question(dialog, "Удалить", 
                                                f"Удалить {email} из группы?",
                                                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
                    if reply == QMessageBox.StandardButton.Yes:
                        group.members.remove(email)
                        self._save_contacts()
                        table.blockSignals(True)
                        table.removeRow(current_row)
                        table.blockSignals(False)
                        layout.itemAt(0).widget().setText(f"Всего: {len(group.members)}")
                        self._refresh_list()
        
        btn_add.clicked.connect(on_add)
        btn_remove.clicked.connect(on_remove)
        btn_close.clicked.connect(dialog.accept)
        dialog.exec()

    def _context_menu(self, pos):
        item = self.list.itemAt(pos)
        if not item:
            return
        
        contact = item.data(Qt.ItemDataRole.UserRole)
        menu = QMenu()
        
        if contact.is_group:
            rename = menu.addAction("Изменить псевдоним")
            members = menu.addAction("Участники группы")
            delete = menu.addAction("Удалить")
            action = menu.exec(self.list.mapToGlobal(pos))
            
            if action == rename:
                self._rename_contact(contact)
            elif action == members:
                self._show_group_members(contact)
            elif action == delete:
                self._delete_contact(contact)
        else:
            rename = menu.addAction("Изменить псевдоним")
            add_group = menu.addAction("Добавить в группу")
            delete = menu.addAction("Удалить")
            action = menu.exec(self.list.mapToGlobal(pos))
            
            if action == rename:
                self._rename_contact(contact)
            elif action == add_group:
                self._add_to_group(contact)
            elif action == delete:
                self._delete_contact(contact)
    
    def _rename_contact(self, contact):
        new_alias, ok = QInputDialog.getText(self, "Переименовать", "Новый псевдоним:", text=contact.alias)
        if ok and new_alias:
            if contact.is_group:
                old_alias = contact.alias
                contact.alias = new_alias
                old_dir = DATA_DIR / old_alias
                new_dir = DATA_DIR / new_alias
                if old_dir.exists() and old_dir != new_dir:
                    old_dir.rename(new_dir)
                self._save_contacts()
            else:
                contact.alias = new_alias
                self._save_contacts()
            self._refresh_list()
    
    def _add_to_group(self, contact):
        groups = [c for c in self.contacts if c.is_group]
        if not groups:
            QMessageBox.information(self, "Информация", "Нет доступных групп")
            return
        
        dialog = QDialog(self)
        dialog.setWindowTitle("Выберите группу")
        layout = QVBoxLayout(dialog)
        
        list_widget = QListWidget()
        for group in groups:
            list_widget.addItem(f"{group.alias} ({len(group.members)} уч.)")
        
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        layout.addWidget(QLabel("Выберите группу для добавления контакта:"))
        layout.addWidget(list_widget)
        layout.addWidget(buttons)
        
        def add_to_selected():
            if list_widget.currentRow() >= 0:
                group = groups[list_widget.currentRow()]
                email_lower = contact.email.lower()
                if email_lower not in [m.lower() for m in group.members]:
                    group.members.append(email_lower)
                    self._save_group_alias(group.groupname, email_lower, contact.alias)
                    self._save_contacts()
                    self._refresh_list()
                    QMessageBox.information(dialog, "Успех", f"Контакт {contact.alias} добавлен в группу {group.alias}")
                else:
                    QMessageBox.warning(dialog, "Внимание", f"Контакт уже есть в группе {group.alias}")
            dialog.accept()
        
        buttons.accepted.connect(add_to_selected)
        buttons.rejected.connect(dialog.reject)
        dialog.exec()
    
    def _select_contact_by_email(self, email):
        email_lower = email.lower()
        for i in range(self.list.count()):
            item = self.list.item(i)
            contact = item.data(Qt.ItemDataRole.UserRole)
            if not contact.is_group and contact.email.lower() == email_lower:
                self.list.setCurrentItem(item)
                self._select_contact(item)
                break
    
    def _delete_contact(self, contact):
        reply = QMessageBox.question(self, "Удалить", f"Удалить {contact.alias} со всей историей?",
                                     QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
        if reply == QMessageBox.StandardButton.Yes:
            dir_path = DATA_DIR / (contact.groupname if contact.is_group else contact.email)
            if dir_path.exists():
                shutil.rmtree(dir_path)
            self.contacts.remove(contact)
            self._save_contacts()
            self._refresh_list()
            if self.current_contact == contact:
                self.current_contact = None
                self.chat.clear()
                self.chat_title.set_title("Не выбран чат")
    
    def _attach(self):
        if not self.current_contact:
            QMessageBox.warning(self, "Ошибка", "Сначала выберите чат")
            return
        
        files, _ = QFileDialog.getOpenFileNames(self, "Выберите файлы")
        if files:
            self.attachments.extend(files)
            self._update_attachments_label()
    
    def _clear_attachments(self):
        self.attachments.clear()
        self._update_attachments_label()
    
    def _update_attachments_label(self):
        if self.attachments:
            filenames = [os.path.basename(f) for f in self.attachments]
            self.attachments_label.setText(f"📎 Вложения: {', '.join(filenames)}")
            self.attachments_label.setVisible(True)
        else:
            self.attachments_label.setVisible(False)
    
    def _send(self):
        if not self.current_contact:
            QMessageBox.warning(self, "Ошибка", "Выберите контакт")
            return
        
        text = self.input.toPlainText().strip()
        if not text and not self.attachments:
            QMessageBox.warning(self, "Ошибка", "Введите сообщение")
            return
        
        if self.client.send_message(self.current_contact, text, self.attachments):
            self._append_message(text, True, self.attachments, time.time(), "Я", [])
            self.input.clear()
            self.attachments.clear()
            self._update_attachments_label()
            self.statusBar().showMessage("Отправлено", 3000)
            # Прокручиваем вниз после отправки
            QTimer.singleShot(100, lambda: self.chat.verticalScrollBar().setValue(
                self.chat.verticalScrollBar().maximum()))
        else:
            QMessageBox.critical(self, "Ошибка", "Не удалось отправить")
    
    def _append_message(self, text, is_outgoing, attachments, msg_time, sender, attachment_paths):
        timestamp = datetime.fromtimestamp(msg_time).strftime("%Y-%m-%d %H:%M:%S")
        direction = "→" if is_outgoing else "←"
        self.chat.append(f"[{timestamp}] {sender} {direction} {text}")
        if attachments:
            self.chat.append(f"📎 Вложения:")
            for i, filename in enumerate(attachments):
                if attachment_paths and i < len(attachment_paths):
                    path = attachment_paths[i]
                    self.chat.append(f"   • {filename} (путь: {path})")
                else:
                    self.chat.append(f"   • {filename}")
    
    def _on_message(self, contact, text, is_outgoing, attachments, msg_time, sender, attachment_paths):
        # Обновляем счетчик непрочитанных для этого контакта
        if contact != self.current_contact:
            key = contact.groupname if contact.is_group else contact.email.lower()
            self.unread_counts[key] = self.unread_counts.get(key, 0) + 1
            self._refresh_list()
        
        if contact == self.current_contact:
            self._append_message(text, False, attachments, msg_time, sender, attachment_paths)
            self.statusBar().showMessage(f"Новое сообщение от {sender}", 3000)
            # Прокручиваем вниз
            self.chat.verticalScrollBar().setValue(self.chat.verticalScrollBar().maximum())
        else:
            self.statusBar().showMessage(f"Новое сообщение от {sender}", 5000)
            self._refresh_list()
    
    def _on_scan_done(self):
        self.statusBar().showMessage("Готов к работе", 5000)
        self._refresh_list()
    
    def closeEvent(self, event):
        # Удаляем временные файлы вложений
        temp_dir = Path("temp_attachments")
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
        self.client.stop()
        event.accept()

if __name__ == "__main__":
    app = QApplication(sys.argv)
    DATA_DIR.mkdir(exist_ok=True)
    Path("temp_attachments").mkdir(exist_ok=True)
    window = MainWindow()
    window.show()
    sys.exit(app.exec())