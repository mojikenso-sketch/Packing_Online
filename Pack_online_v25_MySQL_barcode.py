import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog
import mysql.connector
from mysql.connector import Error
import os
import requests
import re
from io import BytesIO
from PIL import Image, ImageTk
from datetime import datetime, timedelta
import winsound
import ctypes
import pdfplumber
import pandas as pd
import mysql.connector

# --- [NEW] ระบบเสียง ---
import threading
try:
    from gtts import gTTS
    import pygame
    HAS_VOICE = True
except ImportError:
    HAS_VOICE = False

# Try to enable High DPI awareness
try:
    ctypes.windll.shcore.SetProcessDpiAwareness(1)
except Exception:
    pass

try:
    from tkcalendar import DateEntry
    HAS_TKCALENDAR = True
except ImportError:
    HAS_TKCALENDAR = False

try:
    import pandas as pd
    HAS_PANDAS = True
except ImportError:
    HAS_PANDAS = False

# --- สำหรับการสร้าง Barcode PDF ด้วย Font ---
try:
    from reportlab.pdfgen import canvas
    from reportlab.lib.units import cm, mm
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    HAS_REPORTLAB = True
except ImportError:
    HAS_REPORTLAB = False

# --- การตั้งค่าฐานข้อมูล ---
## --- การตั้งค่าฐานข้อมูล MySQL ---
# --- การตั้งค่าฐานข้อมูล ---
## --- การตั้งค่าฐานข้อมูล MySQL ---
#DB_HOST = "192.168.1.121"  # <--- เปลี่ยนเป็นเลข IP ของเครื่องแม่ครับ
DB_HOST = "192.168.161.31"
##DB_HOST = "localhost"       # <--- ถ้าใช้บนเครื่องเดียวกันกับ XAMPP ก็ใช้ localhost ได้เลยครับ
DB_USER = "Any"           # <--- User เริ่มต้นของระบบ XAMPP คือ root
DB_PASS = ""               # <--- Password เริ่มต้นของ XAMPP จะไม่มีรหัสผ่าน (ปล่อยว่างไว้)
DB_NAME = "pack_online"    # <--- ชื่อฐานข้อมูลที่คุณสร้างไว้ (ถูกต้องแล้วครับ)

# --- สร้างโฟลเดอร์ Exports แบบอัตโนมัติ (รองรับไฟล์ .exe) ---
import sys

# เช็คว่ารันผ่านไฟล์ .exe หรือรันผ่านโค้ด .py ปกติ
if getattr(sys, 'frozen', False):
    CURRENT_DIR = os.path.dirname(sys.executable)  # ถ้าเป็น .exe ให้เอาที่อยู่ของไฟล์ .exe
else:
    CURRENT_DIR = os.path.dirname(os.path.abspath(__file__))  # ถ้าเป็น .py ให้เอาที่อยู่ของไฟล์โค้ด

OUTPUT_FOLDER = os.path.join(CURRENT_DIR, "Exports")

if not os.path.exists(OUTPUT_FOLDER):
    os.makedirs(OUTPUT_FOLDER)

# --- Modern Color Palette ---
COLOR_BG = "#f4f6f9"
COLOR_WHITE = "#ffffff"
COLOR_PRIMARY = "#24c293"
COLOR_SUCCESS = "#28a745"
COLOR_DANGER = "#dc3545"
COLOR_WARNING = "#ffc107"
COLOR_TEXT = "#343a40"

FONT_MAIN = ("Segoe UI", 12)
FONT_HEADER = ("Segoe UI", 14, "bold")
FONT_BIG = ("Segoe UI", 16, "bold")
FONT_INPUT = ("Segoe UI", 16)

class ZortWMSApp:
    def normalize_barcode(self, s):
        s = "" if s is None else str(s)
        s = s.strip()
        s = re.sub(r'[^0-9a-zA-Z]+', '', s)
        return s.lower()

    def refresh_barcode_lookup(self):
        self.barcode_lookup = {}
        try:
            self.cursor.execute("SELECT barcode, box_barcode, base_name, qty_per_scan, sku, stock_sku FROM product_barcodes")
            for bc, box_bc, base, qty, sku, stock_sku in self.cursor.fetchall():
                bc_n = self.normalize_barcode(bc)
                box_bc_n = self.normalize_barcode(box_bc)
                
                # ลำดับความสำคัญ: 1.ชื่อในสต็อก(ตั้งเอง) -> 2.Target(แพลตฟอร์ม) -> 3.ชื่อกลาง
                target_stock_name = (stock_sku or sku or base or "").strip().upper()
                qty_n = int(qty) if qty else 1
                
                # ถ้ายิงบาร์โค้ดกล่อง
                if box_bc_n and target_stock_name:
                    self.barcode_lookup[box_bc_n] = (target_stock_name, qty_n)
                    
                # ถ้ายิงบาร์โค้ดขวด
                if bc_n and target_stock_name:
                    if bc_n not in self.barcode_lookup:
                        self.barcode_lookup[bc_n] = (target_stock_name, 1)
        except:
            pass

    def cleanup_barcodes_in_db(self):
        try:
            self.cursor.execute("SELECT barcode FROM product_barcodes")
            all_bc = [r[0] for r in self.cursor.fetchall()]
            for bc in all_bc:
                bc_new = self.normalize_barcode(bc)
                if bc_new and bc_new != bc:
                    self.cursor.execute("UPDATE product_barcodes SET barcode=%s WHERE barcode=%s", (bc_new, bc))
                    self.cursor.execute("UPDATE product_barcode_alias SET barcode=%s WHERE barcode=%s", (bc_new, bc))
            self.conn.commit()
        except:
            pass

    def __init__(self, root):
        self.root = root
        self.root.title("ZORT Pack Online - Pick & Pack System v3 + PDF BEST Integrated")
        self.root.state('zoomed')
        self.root.configure(bg=COLOR_BG)

        self.image_references = []
        
        # --- [NEW] เปิดระบบเสียง Pygame และสร้างโฟลเดอร์เก็บเสียง ---
        if HAS_VOICE:
            pygame.mixer.init()
            if not os.path.exists("sounds"): os.makedirs("sounds")
        # ----------------------------------------------------
        
        # --- ตัวแปรสำหรับระบบ Pick & Pack ---
        self.current_step = 0
        self.current_order_no = None
        self.picking_groups = {}     
        self.current_active_box = None 
        self.scanned_sku_log = []
        self.scanned_serials_in_order = set()  
        self.scanned_raw_codes_log = [] 
        self.packing_mode = "normal"  

        self.pdf_current_df = None  

        self.style = ttk.Style()
        self.style.theme_use('clam')
        
        self.style.configure(".", background=COLOR_BG, foreground=COLOR_TEXT) 
        self.style.configure("TFrame", background=COLOR_BG)
        self.style.configure("TLabel", background=COLOR_BG, foreground=COLOR_TEXT, font=FONT_MAIN)
        self.style.configure("TButton", padding=0, borderwidth=0)

        button_styles = {
            "App.TButton": {"bg": "#e0e0e0", "act": "#d0d0d0", "fg": "black"},
            "Primary.TButton": {"bg": COLOR_PRIMARY, "act": "#0056b3", "fg": "white"},
            "Success.TButton": {"bg": COLOR_SUCCESS, "act": "#1e7e34", "fg": "white"},
            "Danger.TButton": {"bg": COLOR_DANGER, "act": "#bd2130", "fg": "white"},
            "Print.TButton": {"bg": "#6f42c1", "act": "#5a32a3", "fg": "white"} 
        }
        for s_name, colors in button_styles.items():
            self.style.configure(s_name, font=("Segoe UI", 11, "bold"), padding=10, 
                                 background=colors["bg"], foreground=colors["fg"], 
                                 borderwidth=3, relief="raised")
            self.style.map(s_name, 
                           background=[("active", colors["act"]), ("pressed", colors["act"])],
                           relief=[("pressed", "sunken"), ("!pressed", "raised")])

        self.style.configure("TNotebook", background=COLOR_BG, tabposition='n')
        self.style.configure("TNotebook.Tab", padding=[20, 10], font=FONT_HEADER, background="#dae0e5")
        self.style.map("TNotebook.Tab", background=[("selected", COLOR_WHITE)], foreground=[("selected", COLOR_PRIMARY)])
        self.style.configure("Treeview", background=COLOR_WHITE, fieldbackground=COLOR_WHITE, foreground=COLOR_TEXT, rowheight=40, font=FONT_MAIN)
        
        self.style.configure("Treeview.Heading", font=FONT_HEADER, background=COLOR_PRIMARY, foreground="white", relief="flat")
        self.style.map("Treeview", background=[("selected", "#7cdcae")], foreground=[("selected", "black")])
        self.style.configure("TLabelframe", background=COLOR_BG, borderwidth=1, relief="solid")
        self.style.configure("TLabelframe.Label", background=COLOR_BG, foreground=COLOR_PRIMARY, font=FONT_HEADER)

        if not HAS_TKCALENDAR:
            messagebox.showwarning("แนะนำ", "เพื่อความสวยงามของปฏิทิน กรุณาติดตั้ง tkcalendar")

        self.init_db()
        self.cleanup_barcodes_in_db()
        self.refresh_barcode_lookup()

# ... (โค้ดเดิมที่มีอยู่แล้ว) ...
        self.setup_ui()
        self.load_all_data()
        self.start_auto_refresh()

        # --- [NEW] หน่วงเวลา 1 วินาที (1000 ms) ให้หน้าจอขึ้นมาก่อน แล้วค่อยพูดทักทาย ---
        self.root.after(1000, self.play_random_greeting)

    # ==========================================
    # 🚀 ระบบเสียง (Text-to-Speech)
    # ==========================================
    # ==========================================
    # 🚀 ระบบเสียง (Text-to-Speech) - แก้ไขบั๊กเงียบ
    # ==========================================
    # ==========================================
    # 🚀 ระบบเสียง (Text-to-Speech) - อัปเกรดใช้ Edge AI เร่งสปีดได้
    # ==========================================
    # ==========================================
    # 🚀 ระบบเสียง (Text-to-Speech) - อัปเกรดใช้ Edge AI เร่งสปีดได้ (แก้บั๊ก WinError 2)
    # ==========================================
    # ==========================================
    # 🚀 ระบบเสียง (Text-to-Speech) - อัปเกรดใช้ Edge AI + แก้บั๊กชื่อไฟล์ภาษาไทย (MD5)
    # ==========================================
    def speak_thai(self, text):
        if not HAS_VOICE: return
            
        def play_sound():
            try:
                import re, tempfile, time, subprocess, sys, hashlib, os
                
                # --- [แก้ไขจุดนี้] ล้างเครื่องหมายที่ทำให้ CMD พัง ---
                clean_text = str(text)
                clean_text = clean_text.replace("'", "")     # ลบ ' ออก (เช่น KING'S -> KINGS)
                clean_text = clean_text.replace('"', "")     # ลบ " ออก
                clean_text = clean_text.replace(",", "")     # ลบ , ออก (เช่น 15,000 -> 15000)
                clean_text = clean_text.replace("-", "ขีด")
                clean_text = clean_text.replace("/", "ทับ")
                # ----------------------------------------------

                temp_dir = tempfile.gettempdir()
                text_hash = hashlib.md5(clean_text.encode('utf-8')).hexdigest()
                filename = os.path.join(temp_dir, f"pack_voice_edge_{text_hash}.mp3")
                
                if not os.path.exists(filename):
                    # ใช้ "py" ตามที่เครื่องใหม่คุณรองรับ
                    command = [
                        "py", "-m", "edge_tts", 
                        "--voice", "th-TH-PremwadeeNeural", 
                        "--rate", "+15%", 
                        "--text", clean_text, 
                        "--write-media", filename
                    ]
                    
                    startupinfo = None
                    if os.name == 'nt':
                        startupinfo = subprocess.STARTUPINFO()
                        startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                    
                    subprocess.run(command, startupinfo=startupinfo, check=True)
                
                # ส่วนเล่นเสียง (อย่าลืมใส่ Loop while busy ที่เราคุยกันก่อนหน้าด้วยนะครับ)
                pygame.mixer.music.load(filename)
                pygame.mixer.music.play()
                while pygame.mixer.music.get_busy():
                    time.sleep(0.1)

            except Exception as e:
                print(f"Audio Error: {e}")
        
        import threading
        threading.Thread(target=play_sound, daemon=True).start()
    # ==========================================
    def play_random_greeting(self):
        import random
        
        # 💬 รายการประโยคทักทายฉบับอัปเกรด (คัดมาให้เน้นๆ ครับ)
        greetings = [
            # --- สายพลังและกำลังใจ ---
            "สวัสดีค่ะ พร้อมลุยงานแล้วหรือยังคะ ขอให้วันนี้ยอดทะลุเป้านะคะ",
            "ยินดีต้อนรับค่ะ วันนี้แพ็คของกันกี่ออเดอร์ดีคะ สู้ๆ นะคะ",
            "วันนี้เรามาทำลายสถิติการแพ็คของกันเถอะค่ะ ลุยเลย!",
            "กองทัพออเดอร์มาแล้ว แต่ทีมงานของเราเก่งกว่าเยอะ สู้ๆ ค่ะ",
            "สวัสดีค่ะ วันนี้ขอให้มียอดขายปังๆ ทำงานราบรื่นตลอดวันเลยนะคะ",
            
            # --- สายใส่ใจและห่วงใย ---
            "เริ่มงานกันเถอะค่ะ ถ้าเหนื่อยก็พักดื่มน้ำบ้างนะคะ เป็นกำลังใจให้ค่ะ",
            "สวัสดีค่ะ ขอให้วันนี้เป็นวันที่ดี แพ็คของไม่มีสะดุดนะคะ",
            "ทำงานด้วยรอยยิ้มนะคะ ทีมงานทุกคนคือหัวใจสำคัญของเราค่ะ",
            "วันนี้อากาศดีนะคะ ขอให้สนุกกับการแพ็คสินค้าทุกชิ้นค่ะ",
            

            
            # --- สายสั้นๆ กระชับ (เผื่อรีบ) ---
            "สู้ๆ นะคะทีมงาน วันนี้เต็มที่ไปเลยค่ะ!",
            "ระบบพร้อมลุย คนพร้อมรบ ลุยกันเลยค่ะทุกคน",
            "สวัสดีค่ะ ยินดีต้อนรับกลับสู่ภารกิจแพ็คของส่งความสุขค่ะ",
            "สวัสดีค่ะ ยินดีต้อนรับกลับสู่ภารกิจแพ็คของส่งความสุขค่ะ สู้ๆ!",
            "สวัสดีค่ะ เริ่มงานด้วยความสดใสนะคะ ถ้าเมื่อยอย่าลืมยืดเส้นยืดสายบ้างนะ",
            "พร้อมหรือยังคะวันนี้ เราจะทำให้ทุกออเดอร์ออกไปอย่างสมบูรณ์แบบค่ะ",
            "สวัสดีค่ะ ขอให้วันนี้งานไหลลื่น ไม่มีสะดุดเลยนะคะ",
            "เริ่มงานแล้วอย่าลืมดูแลตัวเองนะคะ ดื่มน้ำบ่อยๆ ค่ะ",
        ]
        
        # สุ่มเลือกมา 1 ประโยค แล้วสั่งให้ระบบพูด
        text = random.choice(greetings)
        self.speak_thai(text)
    # ==========================================
    # --- เริ่มต้นโค้ดส่วนฐานข้อมูลแบบใหม่ (MySQL) ---
    def init_db(self):
        # 1. สร้างคลาสตัวแปลภาษา เพื่อให้โปรแกรมทำงานกับ MySQL ได้โดยไม่ต้องแก้โค้ดจุดอื่น
        class MySQLCursorWrapper:
            def __init__(self, cursor):
                self.cursor = cursor
            def execute(self, query, params=None):
                q = query.replace('?', '%s')
                if "substr(orderdate,7,4)||substr(orderdate,4,2)||substr(orderdate,1,2)" in q:
                    q = q.replace("substr(orderdate,7,4)||substr(orderdate,4,2)||substr(orderdate,1,2)", "CONCAT(SUBSTRING(orderdate,7,4), SUBSTRING(orderdate,4,2), SUBSTRING(orderdate,1,2))")
                q = q.replace("ORDER BY rowid DESC", "")
                
                if params:
                    self.cursor.execute(q, params)
                else:
                    self.cursor.execute(q)
                return self
            def fetchone(self): return self.cursor.fetchone()
            def fetchall(self): return self.cursor.fetchall()
            @property
            def rowcount(self): return self.cursor.rowcount

        class MySQLConnWrapper:
            def __init__(self, raw_conn):
                self.raw_conn = raw_conn
            def cursor(self): return MySQLCursorWrapper(self.raw_conn.cursor(buffered=True))
            def commit(self): self.raw_conn.commit()
            def rollback(self): self.raw_conn.rollback()
            def close(self): self.raw_conn.close()

        # 2. ทำการเชื่อมต่อ XAMPP
        try:
            raw_conn = mysql.connector.connect(
                host=DB_HOST,       # <--- ให้มันดึงเลข IP จากตัวแปรที่คุณตั้งไว้ด้านบน
                user=DB_USER,       # <--- ดึง User จากด้านบน
                password=DB_PASS,   # <--- ดึง Password จากด้านบน
                database=DB_NAME,   # <--- ดึงชื่อฐานข้อมูลจากด้านบน
                charset='utf8mb4'
            )
            # 3. นำตัวแปลภาษาสวมทับเข้าไป
            self.conn = MySQLConnWrapper(raw_conn)
            self.cursor = self.conn.cursor()
            print("✅ เชื่อมต่อฐานข้อมูล MySQL (XAMPP) สำเร็จ 100%!")
        except Exception as e:
            messagebox.showerror("Database Error", f"เชื่อมต่อฐานข้อมูลล้มเหลว กรุณาเปิด XAMPP: {e}")
    # --- สิ้นสุดโค้ดส่วนฐานข้อมูลแบบใหม่ ---
    def export_treeview_to_excel(self, tree, filename_prefix):
        if not HAS_PANDAS: 
            messagebox.showerror("Error", "ไม่พบไลบรารี pandas ไม่สามารถส่งออกได้")
            return
        
        file_path = filedialog.asksaveasfilename(
            defaultextension=".xlsx", 
            filetypes=[("Excel files", "*.xlsx")], 
            initialfile=f"{filename_prefix}_{datetime.now().strftime('%Y%m%d_%H%M')}.xlsx"
        )
        if not file_path: return
        
        try:
            cols = [tree.heading(c)["text"] for c in tree["columns"]]
            data = []
            for item in tree.get_children():
                data.append(tree.item(item)["values"])
                
            df = pd.DataFrame(data, columns=cols)
            df.to_excel(file_path, index=False)
            messagebox.showinfo("สำเร็จ", f"ส่งออกข้อมูลไปยัง {file_path} เรียบร้อย\n(ข้อมูลตรงตามตารางที่แสดงผล 100%)")
        except Exception as e: 
            messagebox.showerror("Error", str(e))

    def start_auto_refresh(self):
        # แก้จาก 300000 เป็น 5000 เพื่อให้มันเริ่มทำงานทันทีภายใน 5 วินาทีแรกครับ
        self.root.after(300000, self.perform_auto_refresh)

    def perform_auto_refresh(self):
        try:
            # 1. บังคับให้ MySQL ล้างตาเพื่อดูข้อมูลล่าสุดเสมอ
            self.conn.commit()
            
            # 2. [หัวใจสำคัญ] รีเฟรช Tab 5 และตัวแปรบาร์โค้ด "ทุกรอบ" (ทุก 10 วินาที)
            # เพื่อให้เครื่องลูกยิงบาร์โค้ดใหม่ที่เครื่องแม่เพิ่งเพิ่มได้ทันที
            self.load_barcode_data()    
            self.refresh_barcode_lookup() 
            
            # 3. ตรวจสอบรอบการรัน สำหรับหัวข้ออื่นๆ
            if not hasattr(self, 'refresh_counter'): self.refresh_counter = 0
            self.refresh_counter += 1
            
            # ถ้าครบ 30 รอบ (รอบละ 10 วินาที = 300 วินาที หรือ 5 นาทีพอดี)
            if self.refresh_counter >= 30: 
                self.load_stock_data()  # [Tab 1] รีเฟรชทุก 5 นาที
                self.load_all_data()    # [Tab 3] รีเฟรชทุก 5 นาที
                self.load_history()     # [Tab 4] รีเฟรชทุก 5 นาที
                
                self.refresh_counter = 0 # รีเซ็ตตัวนับเพื่อเริ่มรอบ 5 นาทีใหม่
                print("System: Full Refresh (Tabs 1,3,4) completed at 5-min mark.")
            else:
                # ถ้ายังไม่ครบ 5 นาที ให้แสดงแค่ว่าซิงค์บาร์โค้ดแล้ว
                print(f"System: Barcode Synced (Cycle {self.refresh_counter}/30)")

        except Exception as e:
            print(f"Auto-refresh Error: {e}")
            
        # 4. ตั้งให้ฟังก์ชันนี้ตื่นขึ้นมาเช็คบาร์โค้ดทุกๆ 10 วินาที (10,000 มิลลิวินาที)
        # วิธีนี้จะทำให้ Tab 5 ไว แต่หน้าอื่นโหลดห่างตามที่เถ้าแก่กำหนดครับ
        self.root.after(10000, self.perform_auto_refresh)

    def copy_selection(self, tree):
        selection = tree.selection()
        if selection:
            item = tree.item(selection[0]); values = item['values']; text = "\t".join(map(str, values))
            self.root.clipboard_clear(); self.root.clipboard_append(text); self.root.update()

    def add_tree_copy_paste(self, tree):
        menu = tk.Menu(tree, tearoff=0)
        def popup(event):
            item_id = tree.identify_row(event.y); column_id = tree.identify_column(event.x); menu.delete(0, "end")
            if item_id:
                tree.selection_set(item_id)
                try: col_index = int(column_id.replace('#', '')) - 1; cell_value = tree.item(item_id)['values'][col_index]
                except: cell_value = ""
                menu.add_command(label=f"คัดลอก: {str(cell_value)[:20]}...", command=lambda: self.copy_to_clipboard(cell_value))
                menu.add_command(label="คัดลอกทั้งแถว", command=lambda: self.copy_selection(tree))
            menu.tk_popup(event.x_root, event.y_root)
        tree.bind("<Button-3>", popup); tree.bind("<Control-c>", lambda e: self.copy_selection(tree))

    def copy_to_clipboard(self, value):
        self.root.clipboard_clear(); self.root.clipboard_append(str(value)); self.root.update()

    def get_image(self, path_or_url, size=(200, 200)):
        try:
            img = None
            if not path_or_url or str(path_or_url).strip() == "None":
                return None
                
            if path_or_url.startswith("http"):
                resp = requests.get(path_or_url, timeout=3)
                img = Image.open(BytesIO(resp.content))
            elif os.path.exists(path_or_url):
                img = Image.open(path_or_url)

            if img:
                w, h = img.size
                target_w, target_h = size
                ratio = min(target_w / w, target_h / h)
                new_w = int(w * ratio)
                new_h = int(h * ratio)
                img = img.resize((new_w, new_h), Image.Resampling.LANCZOS)
                return ImageTk.PhotoImage(img)
            return None
        except: return None

    def setup_ui(self):
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True, padx=10, pady=10)

        self.tab_stock = tk.Frame(self.notebook); self.notebook.add(self.tab_stock, text=" 🏭 จัดการสต็อก (Stock) ")
        self.tab_scan = tk.Frame(self.notebook); self.notebook.add(self.tab_scan, text=" 📦 ตรวจสอบและแพ็ค (Packing) ")
        self.tab_db = tk.Frame(self.notebook); self.notebook.add(self.tab_db, text=" 📂 รายการทั้งหมด (Database) ")
        self.tab_history = tk.Frame(self.notebook); self.notebook.add(self.tab_history, text=" 🕒 ประวัติการทำงาน (History) ")
        self.tab_barcode = tk.Frame(self.notebook); self.notebook.add(self.tab_barcode, text=" 🏷️ ตั้งค่าบาร์โค้ด (Barcode) ")
        self.tab_pdf_best = tk.Frame(self.notebook); self.notebook.add(self.tab_pdf_best, text=" 📄 PDF BEST (Import) ")

        self.setup_tab_stock()
        self.setup_tab_scan()
        self.setup_tab_db()
        self.setup_tab_history()
        self.setup_tab_barcode()
        self.setup_tab_pdf_best()
        self.tab_pending = tk.Frame(self.notebook)
        self.notebook.add(self.tab_pending, text=" 📊 สรุปยอดค้างส่ง (Pending) ")
        self.setup_tab_pending()

    # --- Tab 1: Stock Management ---
    def setup_tab_stock(self):
        paned = tk.PanedWindow(self.tab_stock, orient=tk.HORIZONTAL, sashrelief=tk.RAISED, sashwidth=6)
        paned.pack(fill="both", expand=True, padx=5, pady=5)

        self.left_frame = tk.Frame(paned, bg=COLOR_WHITE, padx=15, pady=15, relief="flat", bd=1)
        paned.add(self.left_frame, minsize=550)

        self.stock_img_frame = ttk.LabelFrame(self.left_frame, text="รูปสินค้า")
        self.stock_img_frame.pack(fill="both", expand=True)

        self.lbl_stock_img = ttk.Label(self.stock_img_frame, text="รอสแกน", anchor="center")
        self.lbl_stock_img.pack(fill="both", expand=True)

        self.right_frame = tk.Frame(paned, padx=10, pady=10, bg=COLOR_BG)
        paned.add(self.right_frame)

        ctrl_frame = tk.Frame(self.right_frame, bg=COLOR_WHITE, padx=15, pady=15)
        ctrl_frame.pack(fill="x", pady=(0, 15))

        r1 = tk.Frame(ctrl_frame, bg=COLOR_WHITE); r1.pack(fill="x", pady=5)
        tk.Label(r1, text="Barcode (ยิงเพื่อรับเข้า):", font=FONT_HEADER, fg=COLOR_PRIMARY, bg=COLOR_WHITE).pack(side="left")
        self.ent_stock_barcode = ttk.Entry(r1, font=FONT_INPUT, width=30)
        self.ent_stock_barcode.pack(side="left", padx=10)
        self.ent_stock_barcode.bind('<Return>', self.on_stock_auto_in)
        self.ent_stock_barcode.focus_set()

        r2 = tk.Frame(ctrl_frame, bg=COLOR_WHITE); r2.pack(fill="x", pady=5)
        tk.Label(r2, text="วันที่ดูข้อมูล:", bg=COLOR_WHITE).pack(side="left")

        if HAS_TKCALENDAR:
            self.date_picker_stock = DateEntry(r2, width=15, background=COLOR_PRIMARY, foreground='white', 
                                               borderwidth=0, date_pattern='dd/mm/yyyy', font=FONT_MAIN, state="normal")
            self.date_picker_stock.pack(side="left", padx=5)
            self.date_picker_stock.bind("<<DateEntrySelected>>", lambda e: self.load_stock_data())
        else:
            self.date_picker_stock = ttk.Entry(r2, width=15, font=FONT_MAIN)
            self.date_picker_stock.insert(0, datetime.now().strftime('%d/%m/%Y'))
            self.date_picker_stock.pack(side="left", padx=5)
            tk.Label(r2, text="(dd/mm/yyyy)").pack(side="left")
            self.date_picker_stock.bind('<Return>', lambda e: self.load_stock_data())

        ttk.Button(r2, text="🔄 รีเฟรช", style="App.TButton", command=self.manual_refresh_stock).pack(side="left", padx=10)
        ttk.Button(r2, text="🗑️ ลบรายการ", style="Danger.TButton", command=self.delete_stock_item).pack(side="left", padx=5)
        
        ttk.Button(r2, text="✏️ ปรับยอดสต็อก", style="Primary.TButton", command=self.adjust_stock_data).pack(side="left", padx=5)

        ttk.Button(r2, text="🧹 ล้างประวัติซีเรียล", style="Danger.TButton", command=self.clear_stock_serials_history).pack(side="left", padx=5)

        tk.Label(r2, text=" รูปแบบ:", bg=COLOR_WHITE, font=FONT_MAIN).pack(side="left", padx=(15, 5))
        self.cbo_stock_display = ttk.Combobox(r2, values=["แสดงเป็น ชิ้น/ขวด", "แสดงเป็น กล่อง"], state="readonly", width=15, font=FONT_MAIN)
        self.cbo_stock_display.current(0)
        self.cbo_stock_display.pack(side="left", padx=5)
        self.cbo_stock_display.bind("<<ComboboxSelected>>", lambda e: self.load_stock_data())

        ttk.Button(r2, text="📤 Export", style="Success.TButton", command=lambda: self.export_treeview_to_excel(self.stock_tree, "Stock_Data")).pack(side="right", padx=5)
        self.stock_footer_frame = tk.Frame(self.right_frame, bg=COLOR_PRIMARY, pady=8)
        self.stock_footer_frame.pack(side="bottom", fill="x", pady=(5, 0))
        self.lbl_stock_total = tk.Label(self.stock_footer_frame, 
                                        text="รวมทั้งหมด:  รับเข้า 0  |  เบิกจ่าย 0  |  คงเหลือ 0",
                                        font=FONT_HEADER, bg=COLOR_PRIMARY, fg="white")
        self.lbl_stock_total.pack(side="right", padx=20)

        tree_container = tk.Frame(self.right_frame, bg=COLOR_WHITE)
        tree_container.pack(side="top", fill="both", expand=True)

        cols = ("name", "daily_in", "daily_out", "qty", "unit", "last")
        self.stock_tree = ttk.Treeview(tree_container, columns=cols, show="headings")

        self.stock_tree.heading("name", text="ชื่อสินค้าเต็ม")
        self.stock_tree.heading("daily_in", text="รับเข้า")
        self.stock_tree.heading("daily_out", text="เบิกจ่าย")
        self.stock_tree.heading("qty", text="คงเหลือ")
        self.stock_tree.heading("unit", text="หน่วย")
        self.stock_tree.heading("last", text="อัปเดตล่าสุด")

        self.stock_tree.column("name", width=400)
        self.stock_tree.column("daily_in", width=100, anchor="center")
        self.stock_tree.column("daily_out", width=100, anchor="center")
        self.stock_tree.column("qty", width=100, anchor="center")
        self.stock_tree.column("unit", width=80, anchor="center")
        self.stock_tree.column("last", width=150, anchor="center")

        vsb = ttk.Scrollbar(tree_container, orient="vertical", command=self.stock_tree.yview)
        self.stock_tree.configure(yscrollcommand=vsb.set)

        self.stock_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        self.add_tree_copy_paste(self.stock_tree)
        self.stock_tree.bind("<<TreeviewSelect>>", self.on_stock_tree_select)
        self.load_stock_data()

    def get_stock_date(self):
        try:
            if HAS_TKCALENDAR:
                return self.date_picker_stock.get_date().strftime('%Y-%m-%d')
            else:
                return datetime.strptime(self.date_picker_stock.get().strip(), '%d/%m/%Y').strftime('%Y-%m-%d')
        except:
            return datetime.now().strftime('%Y-%m-%d')

    def on_stock_auto_in(self, event):
        self.update_stock_manual("IN")

    def update_stock_manual(self, mode):
        raw_code = self.ent_stock_barcode.get().strip()
        if not raw_code:
            return

        if '-' in raw_code and raw_code.lower() != 'a-00':
            base_raw = raw_code.split('-')[0]
        else:
            base_raw = raw_code
            
        barcode = self.normalize_barcode(base_raw)

        if barcode not in ['a', 'a00']:
            try:
                self.cursor.execute("SELECT 1 FROM stock_in_serials WHERE full_barcode=%s", (raw_code,))
                if self.cursor.fetchone():
                    winsound.Beep(500, 800)
                    messagebox.showerror("สแกนซ้ำ!", f"บาร์โค้ดนี้ ({raw_code})\nเคยถูกสแกนรับเข้าสต็อกไปแล้วในระบบครับ!")
                    self.ent_stock_barcode.delete(0, tk.END)
                    return
            except:
                pass

        if '-' in raw_code:
            base_raw = raw_code.split('-')[0]
        else:
            base_raw = raw_code
            
        barcode = self.normalize_barcode(base_raw)
        res = None

        if barcode.lower() in ["duo", "duoset1"]:
            target_base = "DUO SET(SO1+E1H)"
            total_qty = 2
            res = (target_base, total_qty)
        else:
            if hasattr(self, "barcode_lookup"):
                res = self.barcode_lookup.get(barcode)

            if not res:
                try:
                    self.cursor.execute("""
                        SELECT base_name, qty_per_scan
                        FROM product_barcodes
                        WHERE lower(trim(box_barcode)) = %s
                        LIMIT 1
                    """, (barcode,))
                    row_box = self.cursor.fetchone()
                    
                    if row_box and row_box[0]:
                        res = ((row_box[0] or "").strip().upper(), int(row_box[1]) if row_box[1] else 1)
                    else:
                        self.cursor.execute("""
                            SELECT base_name
                            FROM product_barcodes
                            WHERE lower(trim(barcode)) = %s
                            LIMIT 1
                        """, (barcode,))
                        row_bottle = self.cursor.fetchone()
                        if row_bottle and row_bottle[0]:
                            res = ((row_bottle[0] or "").strip().upper(), 1)

                    if res and hasattr(self, "barcode_lookup"):
                        self.barcode_lookup[barcode] = res
                except Exception as e:
                    print("Error lookup:", e)
                    res = None

        if res:
            target_base, total_qty = res
            self.process_stock_transaction(target_base, mode, total_qty, "Scan-IN")
            
            now = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            try:
                self.cursor.execute("INSERT INTO stock_in_serials (full_barcode, base_barcode, timestamp) VALUES (%s, %s, %s)", 
                                    (raw_code, barcode, now))
                self.conn.commit()
            except:
                pass
            
            self.show_product_image(target_base)
            self.highlight_stock_row(target_base)
            self.ent_stock_barcode.delete(0, tk.END)
            self.ent_stock_barcode.focus()
            winsound.Beep(1000, 100)
        else:
            winsound.Beep(500, 500)
            messagebox.showerror("ผิดพลาด", f"ไม่พบข้อมูลบาร์โค้ด: {barcode}")
            self.ent_stock_barcode.delete(0, tk.END)
            self.ent_stock_barcode.focus()

    def highlight_stock_row(self, target_sku):
        for item in self.stock_tree.get_children():
            row_values = self.stock_tree.item(item, 'values')
            if row_values and str(row_values[0]) == str(target_sku):
                self.stock_tree.move(item, '', 0)
                self.stock_tree.selection_set(item)
                self.stock_tree.focus(item)
                self.stock_tree.see(item)
                break

    def show_product_image(self, search_name):
        img_url = None

        try:
            self.cursor.execute("""
                SELECT box_image_url, image_url 
                FROM product_barcodes 
                WHERE stock_sku=%s OR base_name=%s OR sku=%s
                ORDER BY rowid DESC LIMIT 1
            """, (search_name, search_name, search_name))
            res = self.cursor.fetchone()
            
            if res:
                img_url = res[0] if (res[0] and str(res[0]).strip() != "None" and str(res[0]).strip() != "") else res[1]
        except: pass

        if not img_url or str(img_url).strip() == "None" or str(img_url).strip() == "":
            try:
                self.cursor.execute("SELECT image_url FROM products WHERE sku=%s OR name=%s LIMIT 1", (search_name, search_name))
                res = self.cursor.fetchone()
                if res and res[0]: img_url = res[0]
            except: pass

        if img_url and str(img_url).strip() != "None" and str(img_url).strip() != "":
            photo = self.get_image(img_url, size=(700, 700))
            if photo:
                self.lbl_stock_img.config(image=photo, text="")
                self.lbl_stock_img.image = photo
            else:
                self.lbl_stock_img.config(image="", text="Load Error")
        else:
            self.lbl_stock_img.config(image="", text="No Image")

    def on_stock_tree_select(self, event):
        sel = self.stock_tree.selection()
        if sel:
            item = self.stock_tree.item(sel[0])
            base_name = item['values'][0]
            self.show_product_image(base_name)

    def delete_stock_item(self):
        sel = self.stock_tree.selection()
        if not sel: return
        pwd = simpledialog.askstring("รหัสผ่าน", "กรุณาใส่รหัสผ่านเพื่อลบข้อมูล:", show='*')
        if pwd != "121314":
            messagebox.showerror("ผิดพลาด", "รหัสผ่านไม่ถูกต้อง!")
            return

        item = self.stock_tree.item(sel[0])
        sku_val = item['values'][0] if item and item.get('values') else None
        sku_name = "" if sku_val is None else str(sku_val).strip()
        is_none_like = (sku_val is None) or (sku_name == "") or (sku_name.lower() == "none")

        if is_none_like: confirm_txt = "ลบรายการที่เป็น None/ว่าง ทั้งหมด?\n(จะลบออกจาก stock และ stock_history)"
        else: confirm_txt = f"ลบรายการ '{sku_name}'?\n(ข้อมูลจะหายไปทั้งหมด)"

        if not messagebox.askyesno("ยืนยัน", confirm_txt): return

        try:
            if is_none_like:
                self.cursor.execute("DELETE FROM stock WHERE sku IS NULL OR TRIM(sku)='' OR lower(TRIM(sku))='none'")
                self.cursor.execute("DELETE FROM stock_history WHERE sku IS NULL OR TRIM(sku)='' OR lower(TRIM(sku))='none'")
            else:
                self.cursor.execute("DELETE FROM stock WHERE sku=%s", (sku_name,))
                self.cursor.execute("DELETE FROM stock_history WHERE sku=%s", (sku_name,))
            self.conn.commit()
            self.load_stock_data()
            self.lbl_stock_img.config(image="", text="Deleted")
            messagebox.showinfo("สำเร็จ", "ลบข้อมูลเรียบร้อย")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def adjust_stock_data(self):
        sel = self.stock_tree.selection()
        if not sel:
            messagebox.showwarning("เตือน", "กรุณาคลิกเลือกรายการสินค้าในตารางด้านล่าง ที่ต้องการปรับยอดก่อนครับ")
            return
            
        if hasattr(self, 'cbo_stock_display') and "กล่อง" in self.cbo_stock_display.get():
            messagebox.showwarning("เตือน", "กรุณาสลับรูปแบบการแสดงผลเป็น 'ชิ้น/ขวด' (ด้านบนขวา) ก่อนทำการปรับยอด เพื่อความถูกต้องครับ")
            return

        pwd = simpledialog.askstring("รหัสผ่าน", "กรุณาใส่รหัสผ่านเพื่อปรับยอดสต็อก:", show='*')
        if pwd != "121314":
            if pwd is not None: 
                messagebox.showerror("ผิดพลาด", "รหัสผ่านไม่ถูกต้อง!")
            return

        item = self.stock_tree.item(sel[0])
        vals = item['values']
        sku_name = vals[0]
        
        # ดึงยอดปัจจุบันของแต่ละหัวข้อมา
        try: current_in = float(vals[1])
        except: current_in = 0
        try: current_out = float(vals[2])
        except: current_out = 0
        try: current_balance = float(vals[3])
        except: current_balance = 0
            
        current_unit = vals[4]

        # ปรับรูปแบบตัวเลขไม่ให้มีทศนิยมถ้าเป็นจำนวนเต็ม
        disp_in = int(current_in) if current_in.is_integer() else current_in
        disp_out = int(current_out) if current_out.is_integer() else current_out
        disp_balance = int(current_balance) if current_balance.is_integer() else current_balance

        adj_win = tk.Toplevel(self.root)
        adj_win.title("ปรับยอดสต็อก (รับเข้า / เบิกจ่าย)")
        adj_win.geometry("600x500") 
        adj_win.resizable(False, False)
        adj_win.grab_set()

        tk.Label(adj_win, text=f"ปรับยอด: {sku_name[:40]}...", font=("Segoe UI", 14, "bold")).pack(pady=(15, 5))
        tk.Label(adj_win, text=f"คงเหลือในระบบรวม: {disp_balance} {current_unit}", font=("Segoe UI", 12, "bold"), fg=COLOR_SUCCESS).pack(pady=(0, 10))

        # --- 🟢 โซนปรับ ยอดรับเข้า (IN) ---
        frame_in = tk.LabelFrame(adj_win, text=" ปรับแก้ไข ยอดรับเข้า (IN) ", font=("Segoe UI", 10, "bold"), fg=COLOR_PRIMARY, padx=10, pady=5)
        frame_in.pack(fill="x", padx=20, pady=5)

        tk.Label(frame_in, text=f"ยอดรับเข้าปัจจุบัน: {disp_in}", font=("Segoe UI", 10)).pack()
        
        self.new_in_var = tk.DoubleVar(value=disp_in)
        ctrl_in = tk.Frame(frame_in)
        ctrl_in.pack(pady=5)

        def change_in(amount):
            current = self.new_in_var.get()
            new_val = current + amount
            if new_val < 0: new_val = 0 
            self.new_in_var.set(new_val)
            lbl_in.config(text=str(int(new_val) if float(new_val).is_integer() else new_val))

        tk.Button(ctrl_in, text=" -10 ", font=("Segoe UI", 12, "bold"), width=4, bg="#ffc107", command=lambda: change_in(-10)).pack(side="left", padx=5)
        tk.Button(ctrl_in, text=" -1 ", font=("Segoe UI", 12, "bold"), width=3, bg="#dc3545", fg="white", command=lambda: change_in(-1)).pack(side="left", padx=5)
        lbl_in = tk.Label(ctrl_in, text=str(disp_in), font=("Segoe UI", 20, "bold"), width=5, fg=COLOR_PRIMARY)
        lbl_in.pack(side="left", padx=10)
        tk.Button(ctrl_in, text=" +1 ", font=("Segoe UI", 12, "bold"), width=3, bg="#28a745", fg="white", command=lambda: change_in(1)).pack(side="left", padx=5)
        tk.Button(ctrl_in, text=" +10 ", font=("Segoe UI", 12, "bold"), width=4, bg="#17a2b8", fg="white", command=lambda: change_in(10)).pack(side="left", padx=5)

        # --- 🔴 โซนปรับ ยอดเบิกจ่าย (OUT) ---
        frame_out = tk.LabelFrame(adj_win, text=" ปรับแก้ไข ยอดเบิกจ่าย (OUT) ", font=("Segoe UI", 10, "bold"), fg=COLOR_DANGER, padx=10, pady=5)
        frame_out.pack(fill="x", padx=20, pady=5)

        tk.Label(frame_out, text=f"ยอดเบิกจ่ายปัจจุบัน: {disp_out}", font=("Segoe UI", 10)).pack()
        
        self.new_out_var = tk.DoubleVar(value=disp_out)
        ctrl_out = tk.Frame(frame_out)
        ctrl_out.pack(pady=5)

        def change_out(amount):
            current = self.new_out_var.get()
            new_val = current + amount
            if new_val < 0: new_val = 0 
            self.new_out_var.set(new_val)
            lbl_out.config(text=str(int(new_val) if float(new_val).is_integer() else new_val))

        tk.Button(ctrl_out, text=" -10 ", font=("Segoe UI", 12, "bold"), width=4, bg="#ffc107", command=lambda: change_out(-10)).pack(side="left", padx=5)
        tk.Button(ctrl_out, text=" -1 ", font=("Segoe UI", 12, "bold"), width=3, bg="#dc3545", fg="white", command=lambda: change_out(-1)).pack(side="left", padx=5)
        lbl_out = tk.Label(ctrl_out, text=str(disp_out), font=("Segoe UI", 20, "bold"), width=5, fg=COLOR_DANGER)
        lbl_out.pack(side="left", padx=10)
        tk.Button(ctrl_out, text=" +1 ", font=("Segoe UI", 12, "bold"), width=3, bg="#28a745", fg="white", command=lambda: change_out(1)).pack(side="left", padx=5)
        tk.Button(ctrl_out, text=" +10 ", font=("Segoe UI", 12, "bold"), width=4, bg="#17a2b8", fg="white", command=lambda: change_out(10)).pack(side="left", padx=5)

        # --- ฟังก์ชันบันทึก ---
        def confirm_adjust():
            diff_in = self.new_in_var.get() - current_in
            diff_out = self.new_out_var.get() - current_out
            
            # ถ้าไม่ได้ปรับอะไรเลย ให้ปิดหน้าต่างไปเฉยๆ
            if diff_in == 0 and diff_out == 0:
                adj_win.destroy()
                return
                
            try:
                # ถ้ามีการปรับยอดรับเข้า
                if diff_in != 0:
                    adj_qty = int(diff_in) if float(diff_in).is_integer() else diff_in
                    self.process_stock_transaction(sku_name, "IN", adj_qty, "ปรับแก้ไขยอดรับเข้า (Manual)")
                
                # ถ้ามีการปรับยอดเบิกจ่าย
                if diff_out != 0:
                    adj_qty = int(diff_out) if float(diff_out).is_integer() else diff_out
                    self.process_stock_transaction(sku_name, "OUT", adj_qty, "ปรับแก้ไขยอดเบิกจ่าย (Manual)")

                self.highlight_stock_row(sku_name)
                adj_win.destroy()
                winsound.Beep(1000, 200) 
            except Exception as e:
                messagebox.showerror("Error", f"เกิดข้อผิดพลาด:\n{str(e)}", parent=adj_win)

        tk.Button(adj_win, text="💾 ยืนยันยอดใหม่", font=("Segoe UI", 12, "bold"), bg=COLOR_PRIMARY, fg="white", width=20, command=confirm_adjust).pack(pady=15)

    def clear_stock_serials_history(self):
        if not messagebox.askyesno("ยืนยัน", "⚠️ คำเตือนอันตราย!\n\nต้องการล้าง 'ประวัติสต็อกทั้งหมด' ใช่หรือไม่?\n\n(ยอดรับเข้า เบิกจ่าย ยอดคงเหลือ และประวัติกันสแกนซ้ำของ Tab 1 จะถูกล้างกลับเป็น 0 ทั้งหมด!)"):
            return
        
        pwd = simpledialog.askstring("รหัสผ่าน", "กรุณาใส่รหัสผ่านเพื่อยืนยันการล้างข้อมูลทั้งหมด:", show='*')
        if pwd != "121314":
            messagebox.showerror("ผิดพลาด", "รหัสผ่านไม่ถูกต้อง!")
            return

        try:
            self.cursor.execute("DELETE FROM stock_in_serials")
            self.cursor.execute("DELETE FROM stock_history")
            self.cursor.execute("DELETE FROM stock")
            self.conn.commit()
            
            self.load_stock_data()
            messagebox.showinfo("สำเร็จ", "ล้างประวัติและยอดสต็อกทั้งหมดเรียบร้อยแล้ว!\nตารางกลับไปเริ่มต้นที่ 0 ใหม่ทั้งหมดครับ")
        except Exception as e:
            messagebox.showerror("Error", f"เกิดข้อผิดพลาด: {str(e)}")

    # เปลี่ยนบรรทัด def ด้านบนสุดให้รับค่า skip_reload=False
    def process_stock_transaction(self, sku_name, mode, qty, ref, skip_reload=False):
        sku_name = (sku_name or "").strip()
        if not sku_name or sku_name.lower() == "none": return
        now = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        self.cursor.execute("SELECT quantity FROM stock WHERE sku=%s", (sku_name,))
        current = self.cursor.fetchone()
        new_qty = 0
        if current:
            if mode == "IN": new_qty = current[0] + qty
            else: new_qty = current[0] - qty
            self.cursor.execute("UPDATE stock SET quantity=%s, last_update=%s WHERE sku=%s", (new_qty, now, sku_name))
        else:
            if mode == "IN": new_qty = qty
            else: new_qty = -qty
            self.cursor.execute("INSERT INTO stock (sku, name, quantity, last_update) VALUES (%s, %s, %s, %s)", (sku_name, sku_name, new_qty, now))
        self.cursor.execute("INSERT INTO stock_history (sku, type, qty, ref_doc, timestamp) VALUES (%s, %s, %s, %s, %s)", (sku_name, mode, qty, ref, now))
        self.conn.commit()
        
        # --- [แก้จุดนี้] ถ้าไม่ได้สั่ง skip ค่อยโหลดตาราง Tab 1 ---
        if not skip_reload:
            self.load_stock_data()
    def manual_refresh_stock(self):
        try:
            # 1. บังคับให้ MySQL ล้างตาเพื่อดูข้อมูลล่าสุด (สำคัญมาก!)
            self.conn.commit() 
            # 2. สั่งโหลดข้อมูลสต็อกลงตารางใหม่
            self.load_stock_data()
            # 3. ส่งเสียงบอกว่ารีเฟรชสำเร็จ
            winsound.Beep(1000, 100) 
            print("System: Manual refresh Tab 1 success.")
        except Exception as e:
            print(f"Refresh Error: {e}")
    def load_stock_data(self):
        selected_date = self.get_stock_date() 
        end_of_day = selected_date + " 23:59:59"

        for i in self.stock_tree.get_children(): self.stock_tree.delete(i)

        self.cursor.execute("SELECT stock_sku, sku, base_name, unit FROM product_barcodes")
        unit_map = {}
        for b_stock_sku, b_sku, b_base_name, b_unit in self.cursor.fetchall():
            clean_unit = b_unit if b_unit and str(b_unit).strip() != "None" else "-"
            if b_stock_sku: unit_map[str(b_stock_sku).strip().upper()] = clean_unit
            elif b_sku: unit_map[str(b_sku).strip().upper()] = clean_unit
            elif b_base_name: unit_map[str(b_base_name).strip().upper()] = clean_unit

        self.cursor.execute(f"SELECT sku, SUM(qty) FROM stock_history WHERE type='IN' AND timestamp LIKE '{selected_date}%' GROUP BY sku")
        daily_in_map = {r[0]: r[1] for r in self.cursor.fetchall()}

        self.cursor.execute(f"SELECT sku, SUM(qty) FROM stock_history WHERE type='OUT' AND timestamp LIKE '{selected_date}%' GROUP BY sku")
        daily_out_map = {r[0]: r[1] for r in self.cursor.fetchall()}

        self.cursor.execute("SELECT DISTINCT sku FROM stock_history")
        all_skus = [r[0] for r in self.cursor.fetchall()]

        sum_daily_in = 0
        sum_daily_out = 0
        sum_balance = 0

        display_mode = "ขวด"
        if hasattr(self, 'cbo_stock_display') and "กล่อง" in self.cbo_stock_display.get():
            display_mode = "กล่อง"

        for sku in all_skus:
            self.cursor.execute("SELECT SUM(qty) FROM stock_history WHERE type='IN' AND sku=%s AND timestamp <= %s", (sku, end_of_day))
            res_in = self.cursor.fetchone(); total_in_hist = res_in[0] if res_in[0] else 0

            self.cursor.execute("SELECT SUM(qty) FROM stock_history WHERE type='OUT' AND sku=%s AND timestamp <= %s", (sku, end_of_day))
            res_out = self.cursor.fetchone(); total_out_hist = res_out[0] if res_out[0] else 0

            balance_at_date = total_in_hist - total_out_hist

            self.cursor.execute("SELECT last_update FROM stock WHERE sku=%s", (sku,))
            res_last = self.cursor.fetchone(); raw_date = res_last[0] if res_last else ""

            val_daily_in = daily_in_map.get(sku, 0)
            val_daily_out = daily_out_map.get(sku, 0)
            
            val_unit = unit_map.get(str(sku).strip().upper(), "-")

            if display_mode == "กล่อง":
                divisor = 1
                
                m = re.findall(r'_(\d+)', str(sku))
                if m:
                    divisor = int(m[-1])
                elif "DUO SET" in str(sku).upper():
                    divisor = 2

                val_daily_in = val_daily_in / divisor
                val_daily_out = val_daily_out / divisor
                balance_at_date = balance_at_date / divisor
                
                val_daily_in = int(val_daily_in) if float(val_daily_in).is_integer() else round(val_daily_in, 2)
                val_daily_out = int(val_daily_out) if float(val_daily_out).is_integer() else round(val_daily_out, 2)
                balance_at_date = int(balance_at_date) if float(balance_at_date).is_integer() else round(balance_at_date, 2)
                
                val_unit = "กล่อง"

            fmt_date = raw_date
            try:
                dt_obj = datetime.strptime(raw_date, '%Y-%m-%d %H:%M:%S')
                fmt_date = dt_obj.strftime('%d/%m/%Y %H:%M:%S')
            except: pass

            sum_daily_in += val_daily_in
            sum_daily_out += val_daily_out
            sum_balance += balance_at_date

            self.stock_tree.insert("", "end", values=(sku, val_daily_in, val_daily_out, balance_at_date, val_unit, fmt_date))

        def fmt_num(n):
            return f"{int(n):,}" if isinstance(n, int) or float(n).is_integer() else f"{n:,.2f}"

        if hasattr(self, 'lbl_stock_total'):
            self.lbl_stock_total.config(
                text=f"รวมทั้งหมด:  รับเข้า {fmt_num(sum_daily_in)}  |  เบิกจ่าย {fmt_num(sum_daily_out)}  |  คงเหลือรวม {fmt_num(sum_balance)}"
            )

    # --- Tab 2: Scan (รื้อระบบใหม่) ---
    def setup_tab_scan(self):
        self.header_frame = tk.Frame(self.tab_scan, bg=COLOR_WHITE, pady=15)
        self.header_frame.pack(fill="x", padx=10, pady=10)

        self.lbl_status = tk.Label(self.header_frame, text="สถานะ: รอสแกนออเดอร์", font=("Segoe UI", 18, "bold"), fg="grey", bg=COLOR_WHITE)
        self.lbl_status.pack(side="left", padx=10)

        tk.Label(self.header_frame, text="Order:", font=FONT_BIG, bg=COLOR_WHITE, fg="#555").pack(side="left", padx=(50, 5))
        self.lbl_order_val = tk.Label(self.header_frame, text="-", font=("Segoe UI", 20, "bold"), bg=COLOR_BG, fg=COLOR_PRIMARY, width=15, relief="flat")
        self.lbl_order_val.pack(side="left", padx=5)

        scan_frame = tk.Frame(self.tab_scan, pady=10)
        scan_frame.pack(fill="x", padx=20)

        self.lbl_prompt = tk.Label(scan_frame, text="สแกนออเดอร์ / พัสดุ:", font=FONT_HEADER)
        self.lbl_prompt.pack(side="left")
        self.ent_scan = ttk.Entry(scan_frame, font=FONT_INPUT, width=35)
        self.ent_scan.pack(side="left", padx=10)
        self.ent_scan.focus_set(); self.ent_scan.bind('<Return>', self.process_scan)

        ttk.Button(scan_frame, text="❌ เริ่มใหม่", style="Danger.TButton", command=self.reset_scan_process).pack(side="left", padx=10)
        
        # --- [NEW] วางปุ่มทดสอบเสียงตรงนี้ครับ ---
        ttk.Button(scan_frame, text="🔊 ทดสอบเสียง", style="Primary.TButton", command=lambda: self.speak_thai("ทดสอบระบบเสียง หนึ่ง สอง สาม")).pack(side="left", padx=5)
        # ------------------------------------

        split_paned = tk.PanedWindow(self.tab_scan, orient=tk.HORIZONTAL, sashrelief=tk.RAISED, sashwidth=8, bg=COLOR_BG)
        split_paned.pack(fill="both", expand=True, padx=10, pady=5)

        left_panel = tk.LabelFrame(split_paned, text="⏳ รอดำเนินการ (Pending)", bg=COLOR_BG, fg="#dc3545", font=FONT_HEADER)
        self.txt_pending = tk.Text(left_panel, font=("Segoe UI", 14), bg=COLOR_WHITE, relief="flat", padx=10, pady=10)
        self.txt_pending.pack(fill="both", expand=True)
        split_paned.add(left_panel, minsize=400)

        right_panel = tk.LabelFrame(split_paned, text="✅ เสร็จสิ้น (Completed)", bg=COLOR_BG, fg="#28a745", font=FONT_HEADER)
        self.txt_completed = tk.Text(right_panel, font=("Segoe UI", 14), bg=COLOR_WHITE, relief="flat", padx=10, pady=10)
        self.txt_completed.pack(fill="both", expand=True)
        split_paned.add(right_panel, minsize=400)

    def set_packing_mode(self, mode):
        if self.current_step > 0:
            if not messagebox.askyesno("เปลี่ยนโหมด", "กำลังแพ็คออเดอร์อยู่ ต้องการยกเลิกและเปลี่ยนโหมดหรือไม่?"):
                return
            self.reset_scan_process()
        self.packing_mode = mode
        self.update_mode_buttons()

    def update_mode_buttons(self):
        if hasattr(self, 'btn_mode_normal'):
            if self.packing_mode == "normal":
                self.btn_mode_normal.configure(style="Success.TButton")
                self.btn_mode_combined.configure(style="App.TButton")
            else:
                self.btn_mode_normal.configure(style="App.TButton")
                self.btn_mode_combined.configure(style="Success.TButton")

    def reset_scan_process(self):
        self.current_step = 0
        self.current_order_no = None
        self.picking_groups = {}
        self.scanned_sku_log = []
        self.scanned_serials_in_order = set() 
        self.scanned_raw_codes_log = []

        self.lbl_status.config(text="สถานะ: รอสแกนออเดอร์", fg="grey")
        self.lbl_order_val.config(text="-")
        self.lbl_prompt.config(text="สแกนออเดอร์ / พัสดุ:")
        
        self.ent_scan.config(state='normal', background=COLOR_WHITE)
        self.ent_scan.delete(0, tk.END)
        self.ent_scan.focus_set()

        self.txt_pending.config(state="normal")
        self.txt_pending.delete("1.0", tk.END)
        self.txt_pending.config(state="disabled")

        self.txt_completed.config(state="normal")
        self.txt_completed.delete("1.0", tk.END)
        self.txt_completed.config(state="disabled")

    def process_scan(self, event):
        code = self.ent_scan.get().strip()
        self.ent_scan.delete(0, tk.END)
        if not code: return
        
        if self.current_step == 0: 
            self.check_order(code)
        elif self.current_step == 1: 
            self.check_item_barcode(code)

    def check_order(self, order_no):
        clean_order_no = str(order_no).strip().lower()
        
        self.cursor.execute("""
            SELECT number, customername FROM orders 
            WHERE lower(trim(number)) = %s OR lower(trim(tracking_no)) = %s
        """, (clean_order_no, clean_order_no))
        res_order = self.cursor.fetchone()

        if not res_order:
            messagebox.showerror("Error", "ไม่พบ 'เลขออเดอร์' หรือ 'เลขพัสดุ' นี้ในระบบ"); winsound.Beep(500, 500)
            return

        real_order_no = res_order[0]
        
        self.cursor.execute("SELECT sku, name, quantity FROM order_items WHERE order_number=%s", (real_order_no,))
        items = self.cursor.fetchall()
        
        if not items:
            messagebox.showerror("Error", "ไม่พบสินค้าในออเดอร์นี้"); winsound.Beep(500, 500)
            return

        self.picking_groups = {"ALL": {"is_completed": False, "items": {}}}

        for _, name, qty in items:
            clean_name = name.strip()
            
            m = re.search(r'x\s*(\d+)', clean_name.lower())
            multiplier = int(m.group(1)) if m else 1
            real_qty = qty * multiplier

            self.cursor.execute("SELECT barcode FROM product_barcode_alias WHERE alias=%s", (clean_name,))
            bc_res = self.cursor.fetchone()
            target_bc = bc_res[0] if bc_res else None
            
            if target_bc:
                self.cursor.execute("SELECT image_url, base_name FROM product_barcodes WHERE barcode=%s", (target_bc,))
                cfg = self.cursor.fetchone()
            else:
                cfg = None
            
            base_name = str(cfg[1]).strip() if cfg and len(cfg) > 1 and cfg[1] else clean_name
            if not base_name or base_name.lower() == "none":
                base_name = clean_name
                
            item_img = cfg[0] if cfg else ""

            if base_name in self.picking_groups["ALL"]["items"]:
                self.picking_groups["ALL"]["items"][base_name]['req'] += real_qty
            else:
                self.picking_groups["ALL"]["items"][base_name] = {
                    "req": real_qty, 
                    "scanned": 0, 
                    "item_img": item_img,
                    "target_bc": target_bc
                }

        self.current_order_no = real_order_no
        self.current_step = 1
        self.lbl_status.config(text="สถานะ: กำลังแพ็คสินค้า", fg=COLOR_WARNING)
        self.lbl_order_val.config(text=real_order_no)
        self.lbl_prompt.config(text="สแกนสินค้า:")
        self.update_display()
        winsound.Beep(1000, 200)
        
        # =========================================================
        # 🚀 [NEW] ระบบเสียง: อ่านรายการสินค้าและจำนวนที่ต้องหยิบ
        # =========================================================
        items_to_speak = []
        for item_name, info in self.picking_groups["ALL"]["items"].items():
            qty = info['req']
            
            # พยายามหาหน่วยจากฐานข้อมูล (ถ้าไม่มีให้ใช้คำว่า ชิ้น)
            unit = "ชิ้น"
            try:
                self.cursor.execute("SELECT unit FROM product_barcodes WHERE base_name=%s LIMIT 1", (item_name,))
                u_res = self.cursor.fetchone()
                if u_res and u_res[0]: unit = u_res[0]
            except: pass
            
            items_to_speak.append(f"{item_name} {qty} {unit}")
        
        all_items_text = " , ".join(items_to_speak)
        self.speak_thai(f"ออเดอร์นี้ ต้องใส่ {all_items_text} ค่ะ")
        # =========================================================

    def check_box(self, scanned_box_bc):
        raw_box = scanned_box_bc.strip()
        
        if '-' in raw_box:
            raw_box = raw_box.split('-')[0]
            
        box_bc = self.normalize_barcode(raw_box)
        
        if box_bc in self.picking_groups:
            if self.picking_groups[box_bc]["is_completed"]:
                messagebox.showwarning("เตือน", "กล่องนี้แพ็คเสร็จไปแล้วครับ!")
                winsound.Beep(500, 300)
                return
            
            self.current_active_box = box_bc
            self.current_step = 2
            self.lbl_status.config(text=f"สถานะ: กำลังแพ็คกล่อง", fg=COLOR_WARNING)
            self.lbl_box_val.config(text=box_bc.upper())
            self.lbl_prompt.config(text="สแกนสินค้าใส่กล่อง:")
            self.update_display()
            winsound.Beep(1000, 200)
        else:
            messagebox.showerror("Error", f"หยิบกล่องผิด!\nออเดอร์นี้ไม่ต้องการกล่องรหัส: {scanned_box_bc}")
            winsound.Beep(500, 500)

    def check_item_barcode(self, item_barcode):
        raw_code = item_barcode.strip()
        
        if '-' in raw_code and raw_code.lower() != 'a-00':
            base_code_part = raw_code.split('-')[0]
            serial_full = raw_code.upper() 
        else:
            base_code_part = raw_code
            serial_full = None

        barcode = self.normalize_barcode(base_code_part)

        # --- [NEW] เช็คว่าเคยรับเข้าใน Tab 1 หรือยัง (ยกเว้นแค่ a กับ a00) ---
        if barcode.lower() not in ['a', 'a00']:
            check_barcode = serial_full if serial_full else raw_code
            try:
                self.cursor.execute("SELECT 1 FROM stock_in_serials WHERE full_barcode=%s", (check_barcode,))
                if not self.cursor.fetchone():
                    self.speak_thai("บาร์โค้ดนี้ ยังไม่เคยยิงรับเข้าสต็อกค่ะ")
                    messagebox.showerror("ยังไม่รับเข้า!", f"บาร์โค้ดหมายเลข ({check_barcode})\nยังไม่เคยถูกยิงรับเข้าในระบบ (Tab 1)\n\nกรุณานำไปยิงรับเข้าสต็อกก่อนนำมาแพ็คครับ!")
                    winsound.Beep(500, 800)
                    return
            except Exception as e:
                pass
        # --------------------------------------------------------------
        
        if serial_full and barcode not in ['a', 'a00']:
            if serial_full in getattr(self, 'scanned_serials_in_order', set()):
                self.speak_thai("บาร์โค้ดนี้ ถูกสแกนไปแล้วนะคะ โปรดตรวจสอบใหม่ค่ะ")
                messagebox.showerror("สแกนซ้ำ!", f"บาร์โค้ดนี้ ({serial_full})\nถูกสแกนแพ็คไปแล้วในออเดอร์นี้ครับ!")
                winsound.Beep(500, 800)
                return
            try:
                self.cursor.execute("SELECT order_number FROM packed_serials WHERE full_barcode=%s", (serial_full,))
                row = self.cursor.fetchone()
                if row:
                    prev_order = row[0]
                    self.speak_thai("บาร์โค้ดนี้ ถูกแพ็คไปแล้วในออเดอร์อื่นค่ะ")
                    messagebox.showerror("สแกนซ้ำ!", f"บาร์โค้ดนี้ ({serial_full})\nเคยถูกแพ็คส่งไปแล้วในออเดอร์: {prev_order}\nไม่สามารถยิงแพ็คซ้ำได้ครับ!")
                    winsound.Beep(500, 800)
                    return
            except Exception as e: pass
        else:
            base_code_part = raw_code
            serial_full = None

        barcode = self.normalize_barcode(base_code_part)
        active_items = self.picking_groups["ALL"]["items"]
        
        if barcode.lower() in ["duo", "duoset1"]:
            found_1 = None
            found_2 = None
            
            for item_key in active_items.keys():
                if "13,500" in item_key: found_1 = item_key
                if "10,000" in item_key: found_2 = item_key
                
            if found_1 and found_2:
                rem_1 = active_items[found_1]['req'] - active_items[found_1]['scanned']
                rem_2 = active_items[found_2]['req'] - active_items[found_2]['scanned']
                
                if rem_1 > 0 and rem_2 > 0:
                    active_items[found_1]['scanned'] += 1
                    active_items[found_2]['scanned'] += 1
                    
                    self.scanned_sku_log.append("DUO SET(SO1+E1H)")
                    self.scanned_sku_log.append("DUO SET(SO1+E1H)")
                    if serial_full:
                        if not hasattr(self, 'scanned_serials_in_order'): self.scanned_serials_in_order = set()
                        self.scanned_serials_in_order.add(serial_full)
                        
                    if not hasattr(self, 'scanned_raw_codes_log'): self.scanned_raw_codes_log = []
                    self.scanned_raw_codes_log.append(raw_code.upper())
                    
                    order_done = all(i['scanned'] >= i['req'] for i in active_items.values())
                    if order_done:
                        self.picking_groups["ALL"]["is_completed"] = True
                        self.update_display()
                        self.finish_process()
                        return
                    else:
                        winsound.Beep(1500, 100)
                        self.update_display()
                        return
                else:
                    self.speak_thai("สแกนดูโอ้เซ็ตซ้ำ หรือสินค้านี้ถูกแพ็คครบไปแล้วค่ะ")
                    messagebox.showwarning("จำนวนเกิน!", "สแกน Duo ซ้ำ หรือสินค้านี้ถูกแพ็คครบไปแล้วครับ")
                    return
            else:
                self.speak_thai("ออเดอร์นี้ ไม่มีรายการดูโอ้เซ็ตค่ะ")
                messagebox.showerror("ผิดรายการ!", "ออเดอร์นี้ไม่มีรายการ Duo Set (13,500 และ 10,000) ครบทั้งคู่ครับ")
                return

        self.cursor.execute("""
            SELECT base_name, qty_per_scan, sku, stock_sku 
            FROM product_barcodes 
            WHERE lower(trim(barcode))=%s OR lower(trim(box_barcode))=%s
            LIMIT 1
        """, (barcode, barcode))
        res_scan = self.cursor.fetchone()
        
        target_base = None
        final_qty_add = 0
        target_stock_name = None
        
        if res_scan:
            target_base = res_scan[0]
            final_qty_add = res_scan[1] if res_scan[1] else 1
            sku_val = res_scan[2]
            stock_sku_val = res_scan[3]
            
            target_stock_name = (stock_sku_val or sku_val or target_base).strip().upper()
            
        if not target_base:
            self.speak_thai("ไม่พบบาร์โค้ดนี้ในระบบค่ะ")
            messagebox.showerror("ผิดพลาด", "ไม่พบบาร์โค้ดนี้ในระบบ กรุณาตรวจสอบ Tab 5")
            winsound.Beep(500, 800)
            return
            
        matched_item_key = None
        for name_key, info in active_items.items():
            if name_key == target_base:
                matched_item_key = name_key
                break
                
        if matched_item_key:
            item_data = active_items[matched_item_key]
            
            remaining = item_data['req'] - item_data['scanned']
            if final_qty_add > remaining:
                self.speak_thai(f"จำนวนเกินค่ะ สินค้านี้ขาดอีกแค่ {remaining} ชิ้นค่ะ")
                messagebox.showwarning("จำนวนเกิน!", f"คุณยิงบาร์โค้ด (+{final_qty_add}) \nแต่สินค้าขาดอีกแค่ {remaining} ชิ้น")
                winsound.Beep(500, 300)
                return
                
            item_data['scanned'] += final_qty_add
            
            if serial_full:
                if not hasattr(self, 'scanned_serials_in_order'): self.scanned_serials_in_order = set()
                self.scanned_serials_in_order.add(serial_full)
                
            if not hasattr(self, 'scanned_raw_codes_log'): self.scanned_raw_codes_log = []
            self.scanned_raw_codes_log.append(raw_code.upper())
            
            for _ in range(final_qty_add):
                self.scanned_sku_log.append(target_stock_name)

            order_done = all(i['scanned'] >= i['req'] for i in active_items.values())
            if order_done:
                self.picking_groups["ALL"]["is_completed"] = True
                self.update_display()
                self.finish_process()
                return
            else:
                winsound.Beep(1500, 100)
                remaining_after = item_data['req'] - item_data['scanned']
                if remaining_after > 0:
                    self.speak_thai(f"ถูกต้องค่ะ ขาดอีก {remaining_after} ชิ้นค่ะ")
            
            self.update_display()
        else:
            self.speak_thai("หยิบผิดชิ้นค่ะ สินค้านี้ไม่มีในออเดอร์นะคะ")
            messagebox.showerror("ผิดรายการ!", f"ในออเดอร์นี้ไม่มีรายการ:\n{target_base}")
            winsound.Beep(500, 800)

    def finish_process(self):
        self.lbl_status.config(text="สำเร็จ ทั้งออเดอร์!", fg=COLOR_SUCCESS)
        self.root.update_idletasks() # <--- [เพิ่มบรรทัดนี้] บังคับหน้าจออัปเดตย้ายฝั่งทันที ไม่ต้องรอ!
        winsound.Beep(2000, 400)
        self.speak_thai("เรียบร้อยค่ะ ออเดอร์นี้แพ็คครบสมบูรณ์แล้ว")
        
        now = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        total_items = sum(item['req'] for group in self.picking_groups.values() for item in group['items'].values())
        scanned_barcodes_str = ", ".join(getattr(self, 'scanned_raw_codes_log', []))
        
        # 1. บันทึกประวัติลง scan_history
        self.cursor.execute("INSERT INTO scan_history (order_number, box_number, scan_time, total_qty, scanned_barcodes) VALUES (%s,%s,%s,%s,%s)", 
                            (self.current_order_no, "-", now, total_items, scanned_barcodes_str))
        
        # 2. บันทึก Serial Number
        for raw_code in getattr(self, 'scanned_raw_codes_log', []):
            if '-' in raw_code:
                base_code = raw_code.split('-')[0]
                base_bc_norm = self.normalize_barcode(base_code)
                try:
                    self.cursor.execute("INSERT INTO packed_serials (full_barcode, base_barcode, order_number, timestamp) VALUES (%s, %s, %s, %s)", 
                                        (raw_code, base_bc_norm, self.current_order_no, now))
                except: pass

        # 3. ตัดสต็อกสินค้า
        # 3. ตัดสต็อกสินค้า
        for scanned_sku in self.scanned_sku_log:
            # เพิ่ม skip_reload=True เพื่อไม่ให้มันวาดตาราง Tab 1 ใหม่ทุกชิ้นที่สแกน
            self.process_stock_transaction(scanned_sku, "OUT", 1, f"Order {self.current_order_no}", skip_reload=True)
            
        # [เพิ่มบรรทัดนี้] ค่อยสั่งโหลดตาราง Tab 1 แค่ "ครั้งเดียว" หลังจากลูปตัดสต็อกเสร็จหมดแล้ว
        self.load_stock_data()
            
        # 🌟 4. ตัดยอดในตารางฐานข้อมูลหลัก (Tab 3)
            
        # 🌟 4. ตัดยอดในตารางฐานข้อมูลหลัก (Tab 3)
        try:
            self.cursor.execute("UPDATE orders SET status='COMPLETED' WHERE number=%s OR tracking_no=%s", 
                                (self.current_order_no, self.current_order_no))
        except Exception as e:
            print(f"Update orders Error: {e}")

        # 🌟 5. ตัดยอดในตาราง PDF ค้างส่ง (Tab 7) พร้อมรีเฟรชหน้าจอ
        try:
            self.cursor.execute("UPDATE pdf_pending_orders SET status='COMPLETED' WHERE order_no=%s OR tracking_no=%s", 
                                (self.current_order_no, self.current_order_no))
            
            if hasattr(self, 'load_pending_orders'): 
                self.load_pending_orders()
                
        except Exception as e: 
            print(f"Update pdf_pending_orders Error: {e}")
        
        # ยืนยันคำสั่งทั้งหมดลง Database
        self.conn.commit()
        
        # รีโหลดหน้าจอเพื่อเตรียมรับงานต่อไป
        self.load_history()
        self.root.after(2000, self.reset_scan_process)

    def update_display(self):
        self.txt_pending.config(state="normal"); self.txt_pending.delete("1.0", tk.END)
        self.txt_completed.config(state="normal"); self.txt_completed.delete("1.0", tk.END)
        self.image_references = []

        box_data = self.picking_groups.get("ALL")
        if not box_data: return

        for item_name, item_info in box_data["items"].items():
            is_done = item_info['scanned'] >= item_info['req']
            target_txt = self.txt_completed if is_done else self.txt_pending
            
            img_url = item_info.get("item_img")
            
            if not img_url or str(img_url).strip() in ["", "None"]:
                try:
                    self.cursor.execute("""
                        SELECT box_image_url, image_url 
                        FROM product_barcodes 
                        WHERE stock_sku=%s OR base_name=%s OR sku=%s
                        ORDER BY rowid DESC LIMIT 1
                    """, (item_name, item_name, item_name))
                    res = self.cursor.fetchone()
                    if res:
                        img_url = res[0] if (res[0] and str(res[0]).strip() not in ["", "None"]) else res[1]
                except: pass

                if not img_url or str(img_url).strip() in ["", "None"]:
                    try:
                        self.cursor.execute("SELECT image_url FROM products WHERE sku=%s OR name=%s LIMIT 1", (item_name, item_name))
                        res = self.cursor.fetchone()
                        if res and res[0]: img_url = res[0]
                    except: pass
            
            target_txt.insert(tk.END, "  ↳ ")
            photo = self.get_image(img_url, size=(100, 100))
            if photo:
                self.image_references.append(photo) 
                target_txt.image_create(tk.END, image=photo)
                target_txt.insert(tk.END, " ")

            status_mark = "✅" if is_done else "⏳"
            target_txt.insert(tk.END, f"{status_mark} {item_name} ({item_info['scanned']}/{item_info['req']})\n\n")

        self.txt_pending.config(state="disabled")
        self.txt_completed.config(state="disabled")

    # --- Tab 3: Database ---
    def setup_tab_db(self):
        ctrl_frame = tk.Frame(self.tab_db, padx=10, pady=15, bg=COLOR_WHITE)
        ctrl_frame.pack(fill="x", padx=10, pady=10)

        tk.Label(ctrl_frame, text="เลือกตาราง:", bg=COLOR_WHITE).pack(side="left")
        self.table_choice = ttk.Combobox(ctrl_frame, values=["Orders (ออเดอร์)", "Items (สินค้า)", "Products (ข้อมูลรูปภาพ)"], state="readonly", font=FONT_MAIN)
        self.table_choice.current(0)
        self.table_choice.pack(side="left", padx=5)
        self.table_choice.bind("<<ComboboxSelected>>", lambda e: self.load_all_data())

        ttk.Button(ctrl_frame, text="🔄 รีเฟรช", style="App.TButton", command=self.load_all_data).pack(side="left", padx=10)
        ttk.Button(ctrl_frame, text="📤 Export Excel", style="Success.TButton", command=lambda: self.export_treeview_to_excel(self.db_tree, "Database_Data")).pack(side="left", padx=5)
        
        self.lbl_db_count = tk.Label(ctrl_frame, text="รวม: 0", font=FONT_HEADER, bg=COLOR_WHITE, fg=COLOR_TEXT)
        self.lbl_db_count.pack(side="right", padx=10)

        filter_frame = tk.Frame(self.tab_db, padx=10, pady=5, bg=COLOR_BG)
        filter_frame.pack(fill="x", padx=10)
        
        tk.Label(filter_frame, text="🔍 ค้นหาเลขออเดอร์:").pack(side="left")
        self.ent_search_order = ttk.Entry(filter_frame, width=15, font=FONT_MAIN)
        self.ent_search_order.pack(side="left", padx=5)
        self.ent_search_order.bind('<KeyRelease>', lambda e: self.load_all_data())
        
        tk.Label(filter_frame, text="🔍 รายละเอียด:").pack(side="left", padx=(10,0))
        self.ent_search_detail = ttk.Entry(filter_frame, width=20, font=FONT_MAIN)
        self.ent_search_detail.pack(side="left", padx=5)
        self.ent_search_detail.bind('<KeyRelease>', lambda e: self.load_all_data())
        
        tk.Label(filter_frame, text="🚚 ขนส่ง:").pack(side="left", padx=(10,0))
        self.cbo_filter_ship = ttk.Combobox(filter_frame, state="readonly", width=15, font=FONT_MAIN)
        self.cbo_filter_ship.pack(side="left", padx=5)
        self.cbo_filter_ship.bind("<<ComboboxSelected>>", lambda e: self.load_all_data())

        tree_container = tk.Frame(self.tab_db, bg=COLOR_WHITE)
        tree_container.pack(fill="both", expand=True, padx=10, pady=5)
        
        self.db_tree = ttk.Treeview(tree_container, show="headings")
        
        vsb = ttk.Scrollbar(tree_container, orient="vertical", command=self.db_tree.yview)
        hsb = ttk.Scrollbar(tree_container, orient="horizontal", command=self.db_tree.xview)
        self.db_tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        
        self.db_tree.grid(column=0, row=0, sticky='nsew')
        vsb.grid(column=1, row=0, sticky='ns')
        hsb.grid(column=0, row=1, sticky='ew')
        
        tree_container.grid_columnconfigure(0, weight=1)
        tree_container.grid_rowconfigure(0, weight=1)

        self.add_tree_copy_paste(self.db_tree)
        self.db_tree.bind("<Double-1>", self.on_db_double_click)

    def load_all_data(self):
        for i in self.db_tree.get_children(): self.db_tree.delete(i)
        choice = self.table_choice.get()
        if "Orders" in choice:
            self.cursor.execute("SELECT DISTINCT shipping_channel FROM orders")
            ships = ["ทั้งหมด"] + [r[0] for r in self.cursor.fetchall() if r[0]]
            self.cbo_filter_ship['values'] = ships
            sql, params = self.build_orders_query()
            self.cursor.execute(sql, params)
            headings = ("เลขออเดอร์", "วันที่", "ลูกค้า", "รายละเอียดสินค้า", "รวมชิ้น", "ยอดรวม", "สถานะ", "ขนส่ง", "เลขพัสดุ")
        elif "Items" in choice:
            self.cursor.execute("SELECT * FROM order_items ORDER BY rowid DESC")
            headings = ("เลขออเดอร์", "SKU", "ชื่อสินค้า", "จำนวน", "URL รูป")
        else:
            self.cursor.execute("SELECT * FROM products")
            headings = ("SKU", "ชื่อสินค้า", "URL รูปภาพ")

        cols = tuple(f"c{i}" for i in range(len(headings)))
        self.db_tree["columns"] = cols
        
        for i, (c, h) in enumerate(zip(cols, headings)):
            self.db_tree.heading(c, text=h, command=lambda _col=c: self.sort_column(self.db_tree, _col, False))
            
            if h in ["รายละเอียดสินค้า", "ชื่อสินค้า", "URL รูปภาพ"]: 
                self.db_tree.column(c, width=300)
            elif h in ["วันที่", "ลูกค้า", "รวมชิ้น", "ยอดรวม", "สถานะ"]:
                self.db_tree.column(c, width=100, anchor="center") 
            else: 
                self.db_tree.column(c, width=100)

        for r in self.cursor.fetchall():
            row_data = list(r)
            if "Orders" in choice and len(row_data) > 7:
                shipping_channel = str(row_data[7]).strip()
                tracking_number = str(row_data[8]).strip()
                if shipping_channel == "SPX Express" and tracking_number and tracking_number.lower() != "none":
                    row_data[0] = tracking_number  
            
            self.db_tree.insert("", "end", values=tuple(row_data))
            
        self.lbl_db_count.config(text=f"รวม: {len(self.db_tree.get_children())} รายการ")

    def build_orders_query(self):
        sql = "SELECT number, orderdate, customername, order_details, total_qty, amount, status, shipping_channel, tracking_no FROM orders WHERE 1=1"
        params = []
        val_order = self.ent_search_order.get()
        
        if val_order: 
            sql += " AND (number LIKE %s OR tracking_no LIKE %s)"
            params.extend([f"%{val_order}%", f"%{val_order}%"])
            
        val_detail = self.ent_search_detail.get()
        if val_detail: sql += " AND order_details LIKE %s"; params.append(f"%{val_detail}%")
        val_ship = self.cbo_filter_ship.get()
        if val_ship and val_ship != "ทั้งหมด": sql += " AND shipping_channel = %s"; params.append(val_ship)
        sql += " ORDER BY substr(orderdate,7,4)||substr(orderdate,4,2)||substr(orderdate,1,2) DESC"
        return sql, params

    def sort_column(self, tree, col, reverse):
        l = [(tree.set(k, col), k) for k in tree.get_children('')]
        try: l.sort(key=lambda t: datetime.strptime(t[0], "%d/%m/%Y"), reverse=reverse)
        except ValueError:
            try: l.sort(key=lambda t: float(t[0].replace(',','')), reverse=reverse)
            except ValueError: l.sort(key=lambda t: t[0], reverse=reverse)
        for index, (val, k) in enumerate(l): tree.move(k, '', index)
        tree.heading(col, command=lambda: self.sort_column(tree, col, not reverse))

    def on_db_double_click(self, event):
        if self.table_choice.get() != "Orders (ออเดอร์)": return
        region = self.db_tree.identify("region", event.x, event.y)
        if region != "cell": return
        column_id = self.db_tree.identify_column(event.x); item_id = self.db_tree.identify_row(event.y)
        if not item_id: return
        col_index = int(column_id.replace('#', '')) - 1
        if col_index == 5:
            current_value = self.db_tree.item(item_id)['values'][col_index]
            x, y, width, height = self.db_tree.bbox(item_id, column_id)
            entry = tk.Entry(self.db_tree, font=FONT_MAIN); entry.place(x=x, y=y, width=width, height=height); entry.insert(0, current_value); entry.focus_set()
            
            def save_edit(e):
                new_val = entry.get()
                try:
                    order_or_tracking = self.db_tree.item(item_id)['values'][0]
                    self.cursor.execute("UPDATE orders SET amount=%s WHERE number=%s OR tracking_no=%s", (new_val, order_or_tracking, order_or_tracking))
                    self.conn.commit(); self.db_tree.set(item_id, column=column_id, value=new_val); entry.destroy()
                except: pass
                
            entry.bind("<Return>", save_edit); entry.bind("<FocusOut>", lambda e: entry.destroy())

    # --- Tab 4: History ---
    def setup_tab_history(self):
        ctrl_frame = tk.Frame(self.tab_history, padx=10, pady=15, bg=COLOR_WHITE); ctrl_frame.pack(fill="x", padx=10, pady=10)

        tk.Label(ctrl_frame, text="กรองวันที่:", bg=COLOR_WHITE, font=FONT_MAIN).pack(side="left")

        if HAS_TKCALENDAR:
            self.date_picker_hist = DateEntry(ctrl_frame, width=12, background=COLOR_PRIMARY, foreground='white',
                                              borderwidth=0, date_pattern='dd/mm/yyyy', font=FONT_MAIN, state="normal")
            self.date_picker_hist.pack(side="left", padx=5)
            self.date_picker_hist.delete(0, "end")  
            self.date_picker_hist.bind("<<DateEntrySelected>>", lambda e: self.load_history())
        else:
            self.date_picker_hist = ttk.Entry(ctrl_frame, width=12, font=FONT_MAIN)
            self.date_picker_hist.pack(side="left", padx=5)
            self.date_picker_hist.bind('<Return>', lambda e: self.load_history())

        ttk.Button(ctrl_frame, text="📅 ดูทั้งหมด", style="App.TButton", command=self.clear_hist_date).pack(side="left", padx=5)
        
        tk.Label(ctrl_frame, text=" 🔍 ค้นหา:", bg=COLOR_WHITE, font=FONT_MAIN).pack(side="left", padx=(15, 5))
        self.ent_search_hist = ttk.Entry(ctrl_frame, width=20, font=FONT_MAIN)
        self.ent_search_hist.pack(side="left", padx=5)
        self.ent_search_hist.bind('<KeyRelease>', lambda e: self.load_history())

        ttk.Button(ctrl_frame, text="🔄 อัปเดต", style="App.TButton", command=self.load_history).pack(side="left", padx=10)
        ttk.Button(ctrl_frame, text="🗑️ ลบประวัติ", style="Danger.TButton", command=self.delete_history_item).pack(side="left", padx=5)
        
        if hasattr(self, 'clear_old_history'):
            ttk.Button(ctrl_frame, text="🧹 ล้างประวัติเก่า", style="Danger.TButton", command=self.clear_old_history).pack(side="left", padx=5)
            
        ttk.Button(ctrl_frame, text="📤 Export", style="Success.TButton", command=lambda: self.export_treeview_to_excel(self.hist_tree, "History_Data")).pack(side="left", padx=5)

        tree_frame = tk.Frame(self.tab_history, bg=COLOR_WHITE)
        tree_frame.pack(fill="both", expand=True, padx=10, pady=5)

        cols = ("id", "time", "order", "order_date", "box", "customer", "details", "qty", "amount", "shipping", "tracking", "barcodes")
        self.hist_tree = ttk.Treeview(tree_frame, columns=cols, show="headings")
        
        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.hist_tree.yview)
        self.hist_tree.configure(yscrollcommand=vsb.set)
        
        self.hist_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        headings = ("#", "เวลาสแกน", "เลขออเดอร์", "วันที่ออเดอร์", "กล่อง", "ลูกค้า", "รายละเอียด", "จำนวน", "ยอดรวม", "ขนส่ง", "เลขพัสดุ", "บาร์โค้ดขวด")
        for col, title in zip(cols, headings):
            self.hist_tree.heading(col, text=title, command=lambda _col=col: self.sort_column(self.hist_tree, _col, False))
            
            if col in ["details", "customer", "barcodes"]:
                self.hist_tree.column(col, width=200)
            else:
                self.hist_tree.column(col, width=90, anchor="center")
                
        self.add_tree_copy_paste(self.hist_tree)

        self.footer_frame = tk.Frame(self.tab_history, bg=COLOR_PRIMARY, pady=8)
        self.footer_frame.pack(fill="x")
        self.lbl_hist_total = tk.Label(self.footer_frame,
                                       text="รวม: 0 รายการ | 0 กล่อง | 0 ชิ้น | 0.00 บาท",
                                       font=FONT_HEADER, bg=COLOR_PRIMARY, fg="white")
        self.lbl_hist_total.pack(side="right", padx=20)
        self.load_history()

    def clear_hist_date(self):
        self.date_picker_hist.delete(0, "end")
        self.load_history()

    def get_hist_date(self):
        try:
            raw_date = self.date_picker_hist.get().strip()
            if not raw_date:
                return None

            if HAS_TKCALENDAR:
                return self.date_picker_hist.get_date().strftime('%Y-%m-%d')
            else:
                return datetime.strptime(raw_date, '%d/%m/%Y').strftime('%Y-%m-%d')
        except:
            return None

    def load_history(self):
        selected_date = self.get_hist_date()
        
        search_text = ""
        if hasattr(self, 'ent_search_hist'):
            search_text = self.ent_search_hist.get().strip()
            
        for i in self.hist_tree.get_children():
            self.hist_tree.delete(i)

        try:
            query = """
                SELECT h.id, h.scan_time, h.order_number, o.orderdate, h.box_number,
                       o.customername, o.order_details, h.total_qty, o.amount,
                       o.shipping_channel, o.tracking_no, h.scanned_barcodes
                FROM scan_history h
                LEFT JOIN orders o ON h.order_number = o.number
                WHERE 1=1
            """
            params = []

            if selected_date:
                query += f" AND h.scan_time LIKE '{selected_date}%'"
                
            if search_text:
                query += " AND (h.order_number LIKE %s OR o.customername LIKE %s OR o.tracking_no LIKE %s OR h.scanned_barcodes LIKE %s)"
                params.extend([f"%{search_text}%", f"%{search_text}%", f"%{search_text}%", f"%{search_text}%"])

            query += " ORDER BY h.id DESC"

            self.cursor.execute(query, params)
            rows = self.cursor.fetchall()

            sum_txn = 0
            sum_box_calc = 0
            sum_qty = 0
            sum_amt = 0.0

            for r in rows:
                lst = list(r)
                try: lst[1] = datetime.strptime(lst[1], '%Y-%m-%d %H:%M:%S').strftime('%d/%m/%Y %H:%M:%S')
                except: pass

                if len(lst) > 11 and lst[11] is None:
                    lst[11] = ""

                self.hist_tree.insert("", "end", values=tuple(lst))
                sum_txn += 1

                scanned_boxes_str = str(r[4]) if r[4] else ""
                scanned_boxes = [b for b in scanned_boxes_str.split(',') if b.strip()]
                row_box_count = len(scanned_boxes)

                total_qty = r[7] if r[7] else 0

                if total_qty >= 24:
                    expected_boxes = total_qty // 12
                    if expected_boxes > row_box_count:
                        row_box_count = expected_boxes
                
                if row_box_count == 0 and total_qty > 0:
                    row_box_count = 1

                sum_box_calc += row_box_count

                if r[7]: sum_qty += r[7]
                if r[8]:
                    try: sum_amt += float(str(r[8]).replace(',', ''))
                    except: pass

            self.lbl_hist_total.config(
                text=f"รวม: {sum_txn} รายการ | {sum_box_calc} กล่อง | {sum_qty} ชิ้น | {sum_amt:,.2f} บาท"
            )

        except Exception as e:
            pass

    def delete_history_item(self):
        sel = self.hist_tree.selection()
        if not sel:
            messagebox.showwarning("เตือน", "กรุณาเลือกรายการ")
            return

        pwd = simpledialog.askstring("รหัสผ่าน", "กรุณาใส่รหัสผ่านเพื่อลบข้อมูล:", show='*')
        if pwd != "121314":
            messagebox.showerror("ผิดพลาด", "รหัสผ่านไม่ถูกต้อง!")
            return

        if messagebox.askyesno("ยืนยัน", "ลบประวัติ?"):
            for item in sel:
                self.cursor.execute("DELETE FROM scan_history WHERE id=%s", (self.hist_tree.item(item)['values'][0],))
            self.conn.commit()
            self.load_history()

    def clear_old_history(self):
        pwd = simpledialog.askstring("รหัสผ่าน", "ฟังก์ชันเคลียร์ฐานข้อมูลเก่า\nกรุณาใส่รหัสผ่าน:", show='*')
        if pwd != "121314":
            if pwd is not None: messagebox.showerror("ผิดพลาด", "รหัสผ่านไม่ถูกต้อง!")
            return

        date_win = tk.Toplevel(self.root)
        date_win.title("เลือกวันที่ต้องการล้างประวัติ")
        date_win.geometry("400x250")
        date_win.resizable(False, False)
        date_win.grab_set()

        tk.Label(date_win, text="เลือกล้างประวัติจนถึงวันที่:", font=("Segoe UI", 14, "bold")).pack(pady=(20, 5))
        tk.Label(date_win, text="(ข้อมูลแพ็คสินค้าก่อนหน้าและรวมถึงวันที่เลือกจะถูกลบทิ้ง)", font=("Segoe UI", 10), fg="grey").pack(pady=(0, 15))

        self.selected_clear_date = None

        if HAS_TKCALENDAR:
            cal = DateEntry(date_win, width=15, background=COLOR_PRIMARY, foreground='white', 
                            borderwidth=0, date_pattern='dd/mm/yyyy', font=("Segoe UI", 14))
            cal.pack(pady=10)
        else:
            cal = ttk.Entry(date_win, width=15, font=("Segoe UI", 14))
            cal.insert(0, datetime.now().strftime('%d/%m/%Y'))
            cal.pack(pady=10)
            tk.Label(date_win, text="(กรุณาพิมพ์ วว/ดด/ปปปป)", font=("Segoe UI", 9)).pack()

        def confirm_date():
            if HAS_TKCALENDAR:
                self.selected_clear_date = cal.get_date().strftime('%d/%m/%Y')
            else:
                self.selected_clear_date = cal.get().strip()
            date_win.destroy()

        tk.Button(date_win, text="🗑️ ยืนยันวันที่", font=("Segoe UI", 12, "bold"), bg=COLOR_DANGER, fg="white", width=15, command=confirm_date).pack(pady=15)

        self.root.wait_window(date_win)

        date_str = self.selected_clear_date
        if not date_str: return

        try:
            dt_obj = datetime.strptime(date_str, '%d/%m/%Y')
            target_end_of_day = dt_obj.strftime('%Y-%m-%d') + " 23:59:59"
            
            if not messagebox.askyesno("ยืนยันขั้นสุดท้าย", f"⚠️ คำเตือนอันตราย!\n\nระบบกำลังจะลบข้อมูลแพ็คสินค้าทั้งหมด\nตั้งแต่เริ่มต้น จนถึงสิ้นสุดของวันที่ {date_str}\n(ปลดล็อคบาร์โค้ดให้กลับมาใช้ใหม่ได้)\n\nคุณแน่ใจหรือไม่? (ข้อมูลส่วนนี้จะไม่สามารถกู้คืนได้)"):
                return
                
            self.cursor.execute("DELETE FROM packed_serials WHERE timestamp <= %s", (target_end_of_day,))
            packed_del = self.cursor.rowcount
            
            self.cursor.execute("DELETE FROM stock_in_serials WHERE timestamp <= %s", (target_end_of_day,))
            
            self.cursor.execute("DELETE FROM scan_history WHERE scan_time <= %s", (target_end_of_day,))
            scan_del = self.cursor.rowcount
            
            self.conn.commit()
            self.load_history()
            
            messagebox.showinfo("สำเร็จ", f"เคลียร์ฐานข้อมูลเรียบร้อยแล้ว!\n\n- ลบประวัติบาร์โค้ดที่เคยใช้ไป: {packed_del} ดวง\n- ลบประวัติออเดอร์เก่า: {scan_del} รายการ\n\nตอนนี้สามารถนำบาร์โค้ดช่วงเวลาดังกล่าวกลับมาสแกนใหม่ได้แล้วครับ")

        except ValueError:
            messagebox.showerror("Error", "รูปแบบวันที่ไม่ถูกต้อง กรุณาระบุใหม่ เช่น 09/04/2026")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    # --- Tab 5: Barcode ---
    def setup_tab_barcode(self):
        input_frame = ttk.LabelFrame(self.tab_barcode, text=" จับคู่ Barcode สินค้า ", padding=15)
        input_frame.pack(fill="x", padx=10, pady=10)

        tk.Label(input_frame, text="ค้นหา:", font=FONT_MAIN).grid(row=0, column=0, sticky="e", padx=(10, 5))
        self.ent_search_prod = ttk.Entry(input_frame, width=25, font=FONT_MAIN)
        self.ent_search_prod.grid(row=0, column=1, padx=5, pady=5, sticky="w")
        self.ent_search_prod.bind('<KeyRelease>', self.filter_products)

        top_btn_frame = tk.Frame(input_frame)
        top_btn_frame.grid(row=0, column=2, columnspan=4, sticky="w", padx=10)
        
        ttk.Button(top_btn_frame, text="👁️ หน้าแสดงผลปกติ", style="App.TButton", command=self.show_normal_view).pack(side="left", padx=5)
        ttk.Button(top_btn_frame, text="📊 แสดงสรุปตามชื่อกลาง", style="App.TButton", command=self.show_summary_view).pack(side="left", padx=5)
        ttk.Button(top_btn_frame, text="⚠️ สินค้าที่ยังไม่ได้ตั้งค่า", style="Danger.TButton", command=self.show_unconfigured_view).pack(side="left", padx=5)

        tk.Label(input_frame, text="Target (ชื่อที่ลูกค้าสั่ง):", font=FONT_MAIN).grid(row=1, column=0, sticky="e", padx=(10, 5))
        self.ent_target_sku = ttk.Entry(input_frame, width=25, font=FONT_MAIN)
        self.ent_target_sku.grid(row=1, column=1, padx=5, pady=5, sticky="w")

        tk.Label(input_frame, text="ชื่อกลาง (รวมตะกร้า):", font=FONT_MAIN).grid(row=1, column=2, sticky="e", padx=(10, 5))
        self.ent_base_name = ttk.Entry(input_frame, width=20, font=FONT_MAIN)
        self.ent_base_name.grid(row=1, column=3, padx=5, pady=5, sticky="w")

        tk.Label(input_frame, text="ชื่อในสต็อก (Tab 1):", font=FONT_MAIN, fg=COLOR_PRIMARY).grid(row=1, column=4, sticky="e", padx=(10, 5))
        self.ent_stock_sku = ttk.Entry(input_frame, width=20, font=FONT_MAIN)
        self.ent_stock_sku.grid(row=1, column=5, padx=5, pady=5, sticky="w")

        tk.Label(input_frame, text="Barcode:", font=FONT_MAIN).grid(row=2, column=0, sticky="e", padx=(10, 5))
        self.ent_box_barcode = ttk.Entry(input_frame, width=25, font=FONT_MAIN)
        self.ent_box_barcode.grid(row=2, column=1, padx=5, pady=5, sticky="w")
        self.ent_box_barcode.bind('<Return>', self.save_barcode)

        qty_unit_frame = tk.Frame(input_frame)
        qty_unit_frame.grid(row=2, column=2, columnspan=4, padx=5, pady=5, sticky="w")
        tk.Label(qty_unit_frame, text="จำนวน:", font=FONT_MAIN).pack(side="left")
        self.ent_qty_input = ttk.Entry(qty_unit_frame, width=8, font=FONT_MAIN)
        self.ent_qty_input.pack(side="left", padx=5)
        self.ent_qty_input.insert(0, "1")
        tk.Label(qty_unit_frame, text="หน่วย:", font=FONT_MAIN).pack(side="left", padx=(15, 5))
        self.cbo_unit = ttk.Combobox(qty_unit_frame, values=["ขวด", "กระป๋อง", "ซอง", "ลัง", "กล่อง", "ใบ"], width=10, font=FONT_MAIN)
        self.cbo_unit.pack(side="left")
        self.cbo_unit.current(0)

        tk.Label(input_frame, text="รูปภาพ:", font=FONT_MAIN).grid(row=3, column=0, sticky="e", padx=(10, 5))
        self.ent_box_img_url = ttk.Entry(input_frame, width=25, font=FONT_MAIN)
        self.ent_box_img_url.grid(row=3, column=1, sticky="ew", padx=5, pady=5)
        ttk.Button(input_frame, text="📂 เลือกไฟล์", style="App.TButton", command=lambda: self.browse_image_file(self.ent_box_img_url)).grid(row=3, column=2, padx=5, sticky="w")

        btn_frame = tk.Frame(input_frame)
        btn_frame.grid(row=4, column=0, columnspan=6, pady=15, sticky="w", padx=10)
        
        ttk.Button(btn_frame, text="💾 บันทึก", style="Success.TButton", command=self.save_barcode).pack(side="left", padx=5)
        ttk.Button(btn_frame, text="🗑️ ลบ", style="Danger.TButton", command=self.delete_barcode).pack(side="left", padx=5)
        ttk.Button(btn_frame, text="🔄 รีเซ็ตเลขรัน", style="App.TButton", command=self.reset_serial_number).pack(side="left", padx=5)
        
        self.print_mode_var = tk.StringVar(value="box")

        self.lbl_current_serial_box = tk.Label(btn_frame, text="ปริ้นถึงเบอร์: -", font=("Segoe UI", 13, "bold"), fg=COLOR_DANGER)
        self.lbl_current_serial_box.pack(side="left", padx=(15, 15))
        
        ttk.Button(btn_frame, text="🖨️ ปริ้นบาร์โค้ด (PDF)", style="Print.TButton", command=self.action_export_barcode_pdf).pack(side="left", padx=15)
        
        if hasattr(self, 'action_reprint_barcode_range'):
            ttk.Button(btn_frame, text="🖨️ ปริ้นซ่อม (ระบุช่วง)", style="App.TButton", command=self.action_reprint_barcode_range).pack(side="left", padx=5)

        tree_frame = tk.Frame(self.tab_barcode, bg=COLOR_WHITE)
        tree_frame.pack(fill="both", expand=True, padx=10, pady=5)

        cols = ("alias", "stock_sku", "box_barcode", "base", "qty", "unit", "box_serial", "box_img")
        self.barcode_tree = ttk.Treeview(tree_frame, columns=cols, show="headings")
        
        self.barcode_tree["displaycolumns"] = ("alias", "stock_sku", "box_barcode", "base", "qty", "unit", "box_serial")

        self.barcode_tree.heading("alias", text="Target (ชื่อที่ลูกค้าสั่ง)", command=lambda: self.sort_column(self.barcode_tree, "alias", False))
        self.barcode_tree.heading("stock_sku", text="ชื่อในสต็อก", command=lambda: self.sort_column(self.barcode_tree, "stock_sku", False))
        self.barcode_tree.heading("box_barcode", text="Barcode", command=lambda: self.sort_column(self.barcode_tree, "box_barcode", False))
        self.barcode_tree.heading("base", text="ชื่อกลาง", command=lambda: self.sort_column(self.barcode_tree, "base", False))
        self.barcode_tree.heading("qty", text="จำนวน", command=lambda: self.sort_column(self.barcode_tree, "qty", False))
        self.barcode_tree.heading("unit", text="หน่วย", command=lambda: self.sort_column(self.barcode_tree, "unit", False))
        self.barcode_tree.heading("box_serial", text="ปริ้น(เลขรัน)", command=lambda: self.sort_column(self.barcode_tree, "box_serial", False))
        self.barcode_tree.heading("box_img", text="รูปภาพ", command=lambda: self.sort_column(self.barcode_tree, "box_img", False))

        self.barcode_tree.column("alias", width=250)
        self.barcode_tree.column("stock_sku", width=150, anchor="center")
        self.barcode_tree.column("box_barcode", width=150, anchor="center")
        self.barcode_tree.column("base", width=120, anchor="center")
        self.barcode_tree.column("qty", width=60, anchor="center")
        self.barcode_tree.column("unit", width=60, anchor="center")
        self.barcode_tree.column("box_serial", width=100, anchor="center") 
        self.barcode_tree.column("box_img", width=200)

        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.barcode_tree.yview)
        self.barcode_tree.configure(yscrollcommand=vsb.set)
        
        self.barcode_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        self.add_tree_copy_paste(self.barcode_tree)
        self.barcode_tree.bind("<<TreeviewSelect>>", self.on_product_select)
        
        # --- ดับเบิ้ลคลิกเพื่อเปิดหน้าต่าง Mapping ---
        self.barcode_tree.bind("<Double-1>", self.on_barcode_tree_double_click)
        
        self.load_barcode_data()

    def on_barcode_tree_double_click(self, event):
        sel = self.barcode_tree.selection()
        if not sel: return
        
        item = self.barcode_tree.item(sel[0])
        vals = item['values']
        unconfig_name = vals[0] 
        box_barcode = vals[2] if len(vals) > 2 else ""
        
        # ถ้ามีบาร์โค้ดแล้วจะไม่ขึ้น Popup
        if box_barcode and str(box_barcode).strip() != "" and str(box_barcode).lower() != "none":
            return
        
        map_win = tk.Toplevel(self.root)
        map_win.title("จับคู่สินค้า (Mapping)")
        map_win.geometry("550x280")
        map_win.resizable(False, False)
        map_win.grab_set()
        
        tk.Label(map_win, text="จับคู่รายการที่ยังไม่ได้ตั้งค่า:", font=("Segoe UI", 12, "bold")).pack(pady=(15, 5))
        tk.Label(map_win, text=f"'{unconfig_name}'", font=("Segoe UI", 11, "bold"), fg=COLOR_DANGER, wraplength=500).pack(pady=(0, 15))
        
        tk.Label(map_win, text="เลือกสินค้าหลักที่ต้องการจับคู่ด้วย (สามารถพิมพ์เพื่อค้นหาได้):", font=FONT_MAIN).pack()
        
        options = []
        self.map_barcode_dict = {} 
        
        for row in getattr(self, 'summary_products_cache', []):
            base_name = row[0]
            barcode = row[1]
            stock_sku = row[10] if len(row) > 10 else "" 
            
            if not barcode: continue
            
            display_name = stock_sku if (stock_sku and str(stock_sku).strip() != "") else base_name
            
            display_text = f"{display_name}  [บาร์โค้ด: {barcode}]"
            options.append(display_text)
            self.map_barcode_dict[display_text] = barcode
            
        cbo_map = ttk.Combobox(map_win, values=options, font=FONT_MAIN, width=55)
        cbo_map.pack(pady=10)
        
        def confirm_mapping():
            selected_text = cbo_map.get()
            if not selected_text or selected_text not in self.map_barcode_dict:
                messagebox.showwarning("เตือน", "กรุณาเลือกหรือพิมพ์ชื่อให้ตรงกับในระบบครับ", parent=map_win)
                return
                
            target_barcode = self.map_barcode_dict[selected_text]
            
            try:
                self.cursor.execute("SELECT COUNT(*) FROM product_barcode_alias WHERE alias=%s", (unconfig_name,))
                exists = self.cursor.fetchone()[0] > 0
                
                if exists:
                    self.cursor.execute("UPDATE product_barcode_alias SET barcode=%s WHERE alias=%s", (target_barcode, unconfig_name))
                else:
                    self.cursor.execute("INSERT INTO product_barcode_alias (barcode, alias) VALUES (%s, %s)", (target_barcode, unconfig_name))
                    
                self.conn.commit()
                self.load_barcode_data() 
                map_win.destroy()
                winsound.Beep(1000, 200)
                
            except Exception as e:
                messagebox.showerror("Error", f"เกิดข้อผิดพลาด:\n{str(e)}", parent=map_win)
                
        ttk.Button(map_win, text="💾 บันทึกการจับคู่", style="Success.TButton", command=confirm_mapping).pack(pady=15)

    def browse_image_file(self, entry_widget):
        filename = filedialog.askopenfilename(title="เลือกไฟล์รูปภาพ", filetypes=[("Image files", "*.jpg *.jpeg *.png *.gif")])
        if filename:
            entry_widget.delete(0, tk.END)
            entry_widget.insert(0, filename)
            
    def show_normal_view(self):
        self.current_barcode_view = "normal"
        self.barcode_tree["displaycolumns"] = ("alias", "stock_sku", "box_barcode", "base", "qty", "unit", "box_serial")
        self.filter_products(None)

    def show_summary_view(self):
        self.current_barcode_view = "summary"
        self.barcode_tree["displaycolumns"] = ("base", "stock_sku", "box_barcode", "qty", "unit", "box_serial")
        self.filter_products(None) 

    def show_unconfigured_view(self):
        self.current_barcode_view = "unconfigured"
        self.barcode_tree["displaycolumns"] = ("alias", "stock_sku", "box_barcode", "base", "qty", "unit", "box_serial")
        self.filter_products(None)

    def load_barcode_data(self):
        for i in self.barcode_tree.get_children():
            self.barcode_tree.delete(i)

        try:
            self.cursor.execute("SELECT barcode, base_name, qty_per_scan, unit, image_url, box_barcode, box_image_url, last_serial_number, is_prepack, last_box_serial_number, stock_sku FROM product_barcodes")
        except:
            self.cursor.execute("SELECT barcode, base_name, qty_per_scan, unit, image_url, '' as box_barcode, '' as box_image_url, 0 as last_serial_number, 0 as is_prepack, 0 as last_box_serial_number, '' as stock_sku FROM product_barcodes")

        bc_cfg = {}
        all_existing_barcodes = set()
        for bc, base, qty, unit, img, box_bc, box_img, last_serial, is_prepack, last_box_serial, stock_sku in self.cursor.fetchall():
            clean_bc = str(bc).strip().lower() # ตัดเว้นวรรคและทำเป็นพิมพ์เล็ก
            bc_cfg[clean_bc] = (base or "", qty or 1, unit or "", img or "", box_bc or "", box_img or "", last_serial or 0, is_prepack or 0, last_box_serial or 0, stock_sku or "")
            all_existing_barcodes.add(clean_bc)

        self.cursor.execute("SELECT barcode, alias FROM product_barcode_alias")
        alias_to_barcode = {}
        for bc, al in self.cursor.fetchall():
            if al:
                alias_to_barcode[al] = str(bc).strip().lower()

        display_aliases = set()
        
        self.cursor.execute("SELECT order_details FROM orders")
        rows = self.cursor.fetchall()
        for r in rows:
            if r[0]:
                text = str(r[0]).replace('\r', '').replace('\n', ', ')
                parts = re.split(r',\s+|\s*\+\s*', text)
                for p in parts:
                    clean_name = p.strip()
                    if not clean_name: continue
                    display_aliases.add(clean_name)
                    base_name = re.sub(r'\s*x\s*\d+\s*$', '', clean_name, flags=re.IGNORECASE).strip()
                    if base_name and base_name != clean_name:
                        display_aliases.add(base_name)

        for al in alias_to_barcode.keys():
            display_aliases.add(al)

        # --- [NEW] สร้างตัวดักจับแบบไม่สนพิมพ์เล็กพิมพ์ใหญ่ ---
        lookup_alias_to_bc = {str(k).strip().lower(): v for k, v in alias_to_barcode.items()}

        self.all_products_cache = []
        used_barcodes = set() 

        for al in sorted(display_aliases, key=lambda x: str(x).lower()):
            clean_al = str(al).strip().lower()
            bc = lookup_alias_to_bc.get(clean_al, "")
            
            base = ""; qty = ""; unit = ""; img = ""; box_bc = ""; box_img = ""; last_serial = 0; is_prepack = 0; last_box_serial = 0; stock_sku = ""

            if bc and bc in bc_cfg:
                base, qty, unit, img, box_bc, box_img, last_serial, is_prepack, last_box_serial, stock_sku = bc_cfg[bc]
                used_barcodes.add(bc) 

            self.all_products_cache.append((al, bc, box_bc, base, qty, unit, last_serial, last_box_serial, img, box_img, stock_sku))

        for bc in all_existing_barcodes:
            if bc not in used_barcodes:
                base, qty, unit, img, box_bc, box_img, last_serial, is_prepack, last_box_serial, stock_sku = bc_cfg[bc]
                ghost_name = f"(ไม่มีชื่อเรียก) {base}" 
                self.all_products_cache.append((ghost_name, bc, box_bc, base, qty, unit, last_serial, last_box_serial, img, box_img, stock_sku))

        self.summary_products_cache = []
        for bc in all_existing_barcodes:
            base, qty, unit, img, box_bc, box_img, last_serial, is_prepack, last_box_serial, stock_sku = bc_cfg[bc]
            self.summary_products_cache.append((base, bc, box_bc, base, qty, unit, last_serial, last_box_serial, img, box_img, stock_sku))
        
        self.summary_products_cache.sort(key=lambda x: str(x[3]).lower())
        
        self.refresh_barcode_lookup()
        self.filter_products(None)

    def update_barcode_tree(self, data):
        for i in self.barcode_tree.get_children():
            self.barcode_tree.delete(i)
        for r in data:
            self.barcode_tree.insert("", "end", values=r)

    def filter_products(self, event=None):
        keyword = self.ent_search_prod.get().lower().strip()
        current_view = getattr(self, 'current_barcode_view', 'normal')
        
        if current_view == "summary": source_data = self.summary_products_cache
        else: source_data = self.all_products_cache
            
        filtered = []
        for row in source_data:
            alias, bc, box_bc, base, qty, unit, serial, box_serial, img, box_img, stock_sku = row
            
            if current_view == "unconfigured":
                if box_bc and str(box_bc).strip() != "" and str(box_bc).lower() != "none": continue
            
            if keyword:
                if not ((alias and keyword in str(alias).lower()) or \
                        (stock_sku and keyword in str(stock_sku).lower()) or \
                        (base and keyword in str(base).lower()) or \
                        (box_bc and keyword in str(box_bc).lower())):
                    continue

            display_row = (alias, stock_sku, box_bc, base, qty, unit, box_serial, box_img)
            filtered.append(display_row)

        self.update_barcode_tree(filtered)

    def on_product_select(self, event):
        sel = self.barcode_tree.selection()
        if sel:
            item = self.barcode_tree.item(sel[0])
            vals = item['values']

            alias_val = vals[0]
            stock_sku_val = vals[1]
            box_val = vals[2]
            base_val = vals[3]
            qty_val = vals[4]
            unit_val = vals[5]
            box_serial_val = vals[6] if len(vals) > 6 else 0 
            box_img_val = vals[7] if len(vals) > 7 else ""

            self.ent_target_sku.delete(0, tk.END)
            self.ent_target_sku.insert(0, alias_val)

            self.ent_stock_sku.delete(0, tk.END)
            if stock_sku_val and str(stock_sku_val) != "None":
                self.ent_stock_sku.insert(0, stock_sku_val)

            self.ent_box_barcode.delete(0, tk.END)
            if box_val and str(box_val) != "None":
                self.ent_box_barcode.insert(0, box_val)

            self.ent_base_name.delete(0, tk.END)
            if base_val and str(base_val) != "None":
                self.ent_base_name.insert(0, base_val)

            self.ent_qty_input.delete(0, tk.END)
            self.ent_qty_input.insert(0, qty_val if qty_val else "1")

            if unit_val and str(unit_val) != "None":
                self.cbo_unit.set(unit_val)
            else:
                self.cbo_unit.current(0)

            self.ent_box_img_url.delete(0, tk.END)
            if box_img_val and str(box_img_val) != "None":
                self.ent_box_img_url.insert(0, box_img_val)
                
            self.lbl_current_serial_box.config(text=f"ปริ้นถึงเบอร์: {box_serial_val}")
            self.ent_box_barcode.focus_set()

    def save_barcode(self, event=None):
        new_box_barcode = self.normalize_barcode(self.ent_box_barcode.get())
        new_barcode = new_box_barcode 
        new_base = (self.ent_base_name.get().strip() or "").upper()
        new_stock_sku = self.ent_stock_sku.get().strip().upper() 
        new_unit = self.cbo_unit.get()
        new_img_url = "" 
        new_box_img_url = self.ent_box_img_url.get().strip()

        try: new_qty = int(self.ent_qty_input.get().strip())
        except: new_qty = 1

        if not new_box_barcode:
            messagebox.showwarning("เตือน", "กรุณากรอก Barcode")
            return

        if not new_base:
            new_base = new_box_barcode.upper()

        selection = self.barcode_tree.selection()

        is_prepack = 1 

        if len(selection) > 1:
            if not messagebox.askyesno("ยืนยันแก้ไขกลุ่ม", f"คุณเลือก {len(selection)} รายการ\nต้องการเปลี่ยนให้ทั้งหมดใช้ Barcode: '{new_box_barcode}' ใช่หรือไม่?"): return

            try:
                self.cursor.execute("SELECT last_serial_number, last_box_serial_number FROM product_barcodes WHERE barcode=%s", (new_barcode,))
                row = self.cursor.fetchone()
                old_s = row[0] if row and row[0] else 0
                old_bs = row[1] if row and row[1] else 0

                self.cursor.execute("DELETE FROM product_barcodes WHERE barcode=%s", (new_barcode,))
                self.cursor.execute("""
                    INSERT INTO product_barcodes (barcode, sku, base_name, box_barcode, qty_per_scan, unit, image_url, box_image_url, is_prepack, last_serial_number, last_box_serial_number, stock_sku)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                """, (new_barcode, new_base, new_base, new_box_barcode, new_qty, new_unit, new_img_url, new_box_img_url, is_prepack, old_s, old_bs, new_stock_sku))

                updated_count = 0
                for item_id in selection:
                    vals = self.barcode_tree.item(item_id)['values']
                    target_alias = str(vals[0])

                    if "(ไม่มีชื่อเรียก)" in target_alias: continue
                        
                    self.cursor.execute("SELECT COUNT(*) FROM product_barcode_alias WHERE alias=%s", (target_alias,))
                    exists = self.cursor.fetchone()[0] > 0
                    
                    if exists: self.cursor.execute("UPDATE product_barcode_alias SET barcode=%s WHERE alias=%s", (new_barcode, target_alias))
                    else: self.cursor.execute("INSERT INTO product_barcode_alias (barcode, alias) VALUES (%s, %s)", (new_barcode, target_alias))
                    updated_count += 1

                self.conn.commit()
                self.load_barcode_data()
                
                self.ent_box_barcode.delete(0, tk.END)
                self.ent_target_sku.delete(0, tk.END)
                messagebox.showinfo("สำเร็จ", f"รวมกลุ่ม {updated_count} รายการ เรียบร้อยแล้ว")

            except Exception as e:
                self.conn.rollback()
                messagebox.showerror("Error", f"เกิดข้อผิดพลาด: {str(e)}")

        else:
            alias = self.ent_target_sku.get().strip()
            if not alias: return

            if not new_base: new_base = (alias.split()[0] if alias.split() else alias).upper()

            try:
                self.cursor.execute("SELECT last_serial_number, last_box_serial_number FROM product_barcodes WHERE barcode=%s", (new_barcode,))
                row = self.cursor.fetchone()
                old_s = row[0] if row and row[0] else 0
                old_bs = row[1] if row and row[1] else 0

                self.cursor.execute("DELETE FROM product_barcodes WHERE barcode=%s", (new_barcode,))
                self.cursor.execute("""
                    INSERT INTO product_barcodes (barcode, sku, base_name, box_barcode, qty_per_scan, unit, image_url, box_image_url, is_prepack, last_serial_number, last_box_serial_number, stock_sku)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                """, (new_barcode, new_base, new_base, new_box_barcode, new_qty, new_unit, new_img_url, new_box_img_url, is_prepack, old_s, old_bs, new_stock_sku))

                self.cursor.execute("SELECT barcode FROM product_barcode_alias WHERE alias=%s LIMIT 1", (alias,))
                old = self.cursor.fetchone()
                if old: self.cursor.execute("UPDATE product_barcode_alias SET barcode=%s WHERE alias=%s", (new_barcode, alias))
                else: self.cursor.execute("INSERT INTO product_barcode_alias (barcode, alias) VALUES (%s, %s)", (new_barcode, alias))

                self.conn.commit()
                self.load_barcode_data()
                self.ent_box_barcode.delete(0, tk.END)
            except Exception as e:
                messagebox.showerror("Error", str(e))

    def delete_barcode(self):
        sel = self.barcode_tree.selection()
        if not sel: 
            messagebox.showwarning("เตือน", "กรุณาคลิกเลือกรายการด้านล่างที่ต้องการลบก่อนครับ")
            return
            
        item = self.barcode_tree.item(sel[0])
        vals = item['values']
        
        alias = vals[0]
        barcode = vals[2] 

        if not barcode or str(barcode).lower() == "none" or str(barcode).strip() == "": 
            messagebox.showwarning("เตือน", "รายการนี้ยังไม่มีข้อมูล Barcode ให้ลบครับ")
            return

        if not messagebox.askyesno("ยืนยัน", f"ต้องการลบข้อมูลของ Barcode: '{barcode}' ใช่หรือไม่?"): 
            return

        try:
            if str(alias).startswith("(ไม่มีชื่อเรียก)"):
                self.cursor.execute("DELETE FROM product_barcodes WHERE barcode=%s OR box_barcode=%s", (barcode, barcode))
                self.cursor.execute("DELETE FROM product_barcode_alias WHERE barcode=%s", (barcode,))
            else:
                self.cursor.execute("DELETE FROM product_barcode_alias WHERE barcode=%s AND alias=%s", (barcode, alias))
                
                self.cursor.execute("SELECT COUNT(*) FROM product_barcode_alias WHERE barcode=%s", (barcode,))
                cnt = self.cursor.fetchone()[0]
                if cnt == 0: 
                    self.cursor.execute("DELETE FROM product_barcodes WHERE barcode=%s OR box_barcode=%s", (barcode, barcode))

            self.conn.commit()
            self.cleanup_barcodes_in_db()
            self.refresh_barcode_lookup()
            self.load_barcode_data()
            
            self.ent_box_barcode.delete(0, tk.END)
            self.ent_target_sku.delete(0, tk.END)
            self.ent_base_name.delete(0, tk.END)
            self.ent_stock_sku.delete(0, tk.END)
            
            messagebox.showinfo("สำเร็จ", "ลบข้อมูลบาร์โค้ดเรียบร้อยแล้วครับ")
        except Exception as e:
            messagebox.showerror("Error", f"เกิดข้อผิดพลาด: {str(e)}")

    def reset_serial_number(self):
        sel = self.barcode_tree.selection()
        if not sel: 
            messagebox.showwarning("เตือน", "กรุณาคลิกเลือกรายการสินค้าด้านล่างที่ต้องการรีเซ็ตเลขครับ")
            return
            
        item = self.barcode_tree.item(sel[0])
        vals = item['values']
        alias = vals[0]
        barcode = vals[2] 

        if not barcode or str(barcode) == "None": 
            return
            
        if not messagebox.askyesno("ยืนยัน", f"ต้องการรีเซ็ตเลขปริ้นของสินค้า:\n\n{alias}\n\nให้กลับไปเริ่มที่ 0 ใหม่ ใช่หรือไม่?\n\n(ประวัติกันสแกนซ้ำทั้งหน้าสต็อกและหน้าแพ็คจะถูกล้างด้วย)"): 
            return

        try:
            self.cursor.execute("UPDATE product_barcodes SET last_serial_number=0, last_box_serial_number=0 WHERE barcode=%s", (barcode,))
            
            base_bc_norm = self.normalize_barcode(str(barcode))
            try: self.cursor.execute("DELETE FROM stock_in_serials WHERE base_barcode=%s", (base_bc_norm,))
            except: pass
            try: self.cursor.execute("DELETE FROM packed_serials WHERE base_barcode=%s", (base_bc_norm,))
            except: pass

            self.conn.commit()
            self.load_barcode_data()
            
            self.lbl_current_serial_box.config(text="ปริ้นถึงเบอร์: 0")
            
            messagebox.showinfo("สำเร็จ", "รีเซ็ตเลขขวดและกล่องกลับเป็น 0 เรียบร้อยแล้วครับ!")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def action_export_barcode_pdf(self):
        if not HAS_REPORTLAB:
            messagebox.showerror("Error", "กรุณาติดตั้ง reportlab ก่อนใช้งานฟังก์ชันนี้\n(พิมพ์: pip install reportlab ใน CMD)")
            return

        import os
        import re
        from reportlab.lib.units import cm, mm
        from reportlab.pdfgen import canvas
        from reportlab.graphics.barcode import code128

        print_mode = self.print_mode_var.get()
        selection = self.barcode_tree.selection()

        if print_mode != "boxextra" and not selection:
            messagebox.showwarning("เตือน", "กรุณาเลือกรายการสินค้าที่ต้องการพิมพ์บาร์โค้ด\n(กด Ctrl ค้างไว้เพื่อเลือกหลายรายการ)")
            return

        # ดึงข้อมูลมาเก็บไว้ในตัวแปรก่อน ป้องกัน Auto-Refresh
        selected_data_list = []
        if selection:
            for item_id in selection:
                try:
                    selected_data_list.append(self.barcode_tree.item(item_id)['values'])
                except:
                    pass

        # 🌟 ปรับค่าเริ่มต้นเป็น 10 ดวงให้พอดีกับกระดาษของคุณ
        self.temp_qty = 10  
        ask_window = tk.Toplevel(self.root)
        ask_window.title("ระบุจำนวนพิมพ์")
        ask_window.geometry("350x300")
        ask_window.resizable(False, False)
        ask_window.grab_set()

        tk.Label(ask_window, text="เลือกจำนวนดวงที่ต้องการพิมพ์", font=("Segoe UI", 12, "bold")).pack(pady=(15, 5))
        
        # 🌟 เปลี่ยนข้อความเป็น 10 ดวง
        tk.Label(ask_window, text="(ขยับทีละ 1 หน้า / 10 ดวง)", font=("Segoe UI", 10)).pack()
        
        frame_ctrl = tk.Frame(ask_window)
        frame_ctrl.pack(pady=15)

        lbl_qty = tk.Label(frame_ctrl, text=str(self.temp_qty), font=("Segoe UI", 28, "bold"), width=4, fg=COLOR_PRIMARY)
        
        def change_qty(val):
            self.temp_qty += val
            # 🌟 ล็อคขั้นต่ำไว้ที่ 10 ดวง
            if self.temp_qty < 10: self.temp_qty = 10 
            lbl_qty.config(text=str(self.temp_qty))

        # 🌟 ปุ่มเปลี่ยนให้บวกลบทีละ 10
        tk.Button(frame_ctrl, text=" - ", font=("Segoe UI", 16, "bold"), width=3, bg="#e0e0e0", 
                  command=lambda: change_qty(-10)).pack(side="left", padx=10)
        lbl_qty.pack(side="left")
        tk.Button(frame_ctrl, text=" + ", font=("Segoe UI", 16, "bold"), width=3, bg="#e0e0e0", 
                  command=lambda: change_qty(10)).pack(side="left", padx=10)

        self.confirmed_qty = None
        def confirm():
            self.confirmed_qty = self.temp_qty
            ask_window.destroy()

        btn_ok = tk.Button(ask_window, text="ตกลง (OK)", font=("Segoe UI", 10, "bold"), 
                           bg=COLOR_SUCCESS, fg="white", width=12, command=confirm)
        btn_ok.pack(pady=15)
        
        self.root.wait_window(ask_window)
        
        if self.confirmed_qty is None: return 
        qty_per_item = self.confirmed_qty

        is_multiple = (print_mode != "boxextra" and len(selected_data_list) > 1)

        if is_multiple:
            save_path = filedialog.askdirectory(title="เลือกโฟลเดอร์สำหรับบันทึกไฟล์ PDF (แยกไฟล์ตามสินค้า)")
            if not save_path: return
        else:
            default_name = f"Barcode1D_{datetime.now().strftime('%Y%m%d_%H%M')}.pdf"
            if print_mode != "boxextra" and len(selected_data_list) == 1:
                vals = selected_data_list[0]
                stock_sku = str(vals[1])
                alias_name = str(vals[0])
                file_base = stock_sku if (stock_sku and stock_sku != "None" and str(stock_sku).strip() != "") else alias_name
                safe_file_base = re.sub(r'[\\/*?:"<>|]', "", file_base)
                default_name = f"{safe_file_base}.pdf"

            save_path = filedialog.asksaveasfilename(
                title="บันทึกไฟล์ PDF",
                defaultextension=".pdf",
                filetypes=[("PDF Files", "*.pdf")],
                initialfile=default_name
            )
            if not save_path: return

        try:
            page_w = 10.0 * cm  
            # 🌟 หดความสูงของ PDF ลงเหลือ 11 cm เพื่อให้พอดีกับหน้ากระดาษคุณ
            page_h = 11.0 * cm  
            margin_x, margin_y = 0.4 * cm, 0.2 * cm  
            gap_x, gap_y = 0.4 * cm, 0.2 * cm     
            sticker_w = (page_w - (2 * margin_x) - gap_x) / 2
            sticker_h = 1.9 * cm 
            
            # 🌟 ปรับให้ปริ้นแค่ 5 แถว (10 ดวง)
            max_cols, max_rows = 2, 5         
            
            count_items = 0
            total_labels = 0
            bc_height = 0.8 * cm

            if print_mode == "boxextra":
                c = canvas.Canvas(save_path, pagesize=(page_w, page_h))
                c.setViewerPreference('PrintScaling', 'None')
                col_idx = 0
                row_idx = 0
                barcode_val = "boxextra"
                for _ in range(qty_per_item):
                    cell_x = margin_x + (col_idx * (sticker_w + gap_x))
                    cell_y = page_h - margin_y - sticker_h - (row_idx * (sticker_h + gap_y))

                    barcode_text = barcode_val.upper()
                    
                    offset_x = 0.4 * cm if col_idx == 0 else -0.2 * cm
                    offset_y = 0.7 * cm if row_idx < 5 else 0

                    barcode_obj = code128.Code128(barcode_text, barHeight=bc_height, barWidth=0.5)
                    real_bc_width = barcode_obj.width
                    
                    x_pos = cell_x + (sticker_w - real_bc_width) / 2 + offset_x
                    y_pos = cell_y + 4 * mm + offset_y

                    barcode_obj.drawOn(c, x_pos, y_pos)

                    c.saveState()
                    c.setFillColorRGB(0, 0, 0)
                    c.setFont("Helvetica", 9)  
                    hr_width = c.stringWidth(barcode_text, "Helvetica", 9)
                    c.drawString(cell_x + (sticker_w - hr_width) / 2 + offset_x, cell_y + 1.5 * mm + offset_y, barcode_text)
                    c.restoreState()
                    
                    col_idx += 1
                    if col_idx >= max_cols:
                        col_idx = 0
                        row_idx += 1
                        if row_idx >= max_rows:
                            c.showPage()
                            col_idx, row_idx = 0, 0
                c.save()
                count_items = 1
                total_labels = qty_per_item
                
                messagebox.showinfo("สำเร็จ", f"สร้างไฟล์ PDF เรียบร้อย!\nรวมทั้งหมด: {total_labels} ดวง")
                try: os.startfile(save_path)
                except: pass

            else:
                for vals in selected_data_list:
                    primary_barcode = str(vals[2])
                    barcode_val = str(vals[2])
                    if not barcode_val or barcode_val == "None": continue

                    stock_sku = str(vals[1])
                    alias_name = str(vals[0])

                    file_base = stock_sku if (stock_sku and stock_sku != "None" and str(stock_sku).strip() != "") else alias_name
                    safe_file_base = re.sub(r'[\\/*?:"<>|]', "", file_base)

                    if is_multiple:
                        item_file_path = os.path.join(save_path, f"{safe_file_base}.pdf")
                    else:
                        item_file_path = save_path

                    c = canvas.Canvas(item_file_path, pagesize=(page_w, page_h))
                    c.setViewerPreference('PrintScaling', 'None')

                    col_idx = 0
                    row_idx = 0

                    current_serial = 0
                    try:
                        self.cursor.execute("SELECT last_box_serial_number FROM product_barcodes WHERE barcode=%s", (primary_barcode,))
                        res_serial = self.cursor.fetchone()
                        current_serial = int(res_serial[0]) if res_serial and res_serial[0] is not None else 0
                    except: pass

                    for _ in range(qty_per_item):
                        cell_x = margin_x + (col_idx * (sticker_w + gap_x))
                        cell_y = page_h - margin_y - sticker_h - (row_idx * (sticker_h + gap_y))

                        current_serial += 1
                        current_barcode = f"{barcode_val}-{current_serial:02d}"

                        barcode_text = current_barcode.upper()
                        
                        offset_x = 0.4 * cm if col_idx == 0 else -0.2 * cm
                        offset_y = 0.7 * cm if row_idx < 5 else 0

                        barcode_obj = code128.Code128(barcode_text, barHeight=bc_height, barWidth=0.5)
                        real_bc_width = barcode_obj.width
                        
                        x_pos = cell_x + (sticker_w - real_bc_width) / 2 + offset_x
                        y_pos = cell_y + 4 * mm + offset_y

                        barcode_obj.drawOn(c, x_pos, y_pos)

                        c.saveState()
                        c.setFillColorRGB(0, 0, 0)
                        c.setFont("Helvetica", 9)  
                        hr_width = c.stringWidth(barcode_text, "Helvetica", 9)
                        c.drawString(cell_x + (sticker_w - hr_width) / 2 + offset_x, cell_y + 1.5 * mm + offset_y, barcode_text)
                        c.restoreState()
                        
                        col_idx += 1
                        if col_idx >= max_cols:
                            col_idx = 0
                            row_idx += 1
                            if row_idx >= max_rows:
                                c.showPage()
                                col_idx, row_idx = 0, 0
                    
                    c.save() 
                    
                    count_items += 1
                    total_labels += qty_per_item
                    
                    try:
                        self.cursor.execute("UPDATE product_barcodes SET last_box_serial_number=%s WHERE barcode=%s", (current_serial, primary_barcode))
                        self.conn.commit()
                    except: pass

                self.load_barcode_data()
                if is_multiple:
                    messagebox.showinfo("สำเร็จ", f"สร้างไฟล์ PDF แยกตามสินค้า ({count_items} ไฟล์) เรียบร้อย!\nบันทึกไว้ที่โฟลเดอร์:\n{save_path}\nรวมทั้งหมด: {total_labels} ดวง")
                    try: os.startfile(save_path) 
                    except: pass
                else:
                    messagebox.showinfo("สำเร็จ", f"สร้างไฟล์ PDF เรียบร้อย!\nจำนวนรายการสินค้า: {count_items}\nรวมทั้งหมด: {total_labels} ดวง")
                    try: os.startfile(save_path)
                    except: pass

        except Exception as e:
            messagebox.showerror("Error", f"เกิดข้อผิดพลาดในการสร้าง PDF:\n{str(e)}")

    def action_reprint_barcode_range(self):
        if not HAS_REPORTLAB:
            messagebox.showerror("Error", "กรุณาติดตั้ง reportlab ก่อนใช้งานฟังก์ชันนี้")
            return

        import os
        from reportlab.lib.units import cm, mm
        from reportlab.pdfgen import canvas
        from reportlab.graphics.barcode import code128

        selection = self.barcode_tree.selection()
        if not selection:
            messagebox.showwarning("เตือน", "กรุณาคลิกเลือกรายการสินค้าด้านล่างที่ต้องการปริ้นซ่อม (1 รายการ)")
            return
        if len(selection) > 1:
            messagebox.showwarning("เตือน", "กรุณาเลือกปริ้นซ่อมทีละ 1 รายการครับ")
            return

        item_id = selection[0]
        vals = self.barcode_tree.item(item_id)['values']
        primary_barcode = str(vals[2]) 
        alias_name = str(vals[0])

        if not primary_barcode or primary_barcode == "None":
            messagebox.showwarning("เตือน", "รายการนี้ไม่มีบาร์โค้ดให้ปริ้นครับ")
            return

        ask_window = tk.Toplevel(self.root)
        ask_window.title("ระบุหมายเลขดวงที่ต้องการปริ้นซ่อม")
        ask_window.geometry("400x250")
        ask_window.resizable(False, False)
        ask_window.grab_set()

        tk.Label(ask_window, text=f"ปริ้นซ่อม: {alias_name[:20]}...", font=("Segoe UI", 12, "bold")).pack(pady=(15, 5))
        tk.Label(ask_window, text="(พิมพ์เลขดวง เช่น 76-88 หรือ 5, 8, 10-15)", font=("Segoe UI", 10)).pack(pady=(0, 10))
        
        ent_range = ttk.Entry(ask_window, font=FONT_MAIN, width=25)
        ent_range.pack(pady=10)
        ent_range.focus_set()
        
        self.reprint_numbers = []
        def confirm(event=None):
            raw_text = ent_range.get().strip()
            if not raw_text: return
            
            try:
                nums = set()
                for part in raw_text.split(','):
                    part = part.strip()
                    if not part: continue
                    if '-' in part:
                        s, e = part.split('-', 1)
                        for i in range(int(s), int(e) + 1):
                            nums.add(i)
                    else:
                        nums.add(int(part))
                
                self.reprint_numbers = sorted(list(nums))
                if not self.reprint_numbers: return
                ask_window.destroy()
            except Exception:
                messagebox.showerror("Error", "รูปแบบตัวเลขไม่ถูกต้อง กรุณาระบุใหม่\n(ตัวอย่าง: 76-88 หรือ 5, 10)", parent=ask_window)
                
        ent_range.bind("<Return>", confirm)
        btn_ok = tk.Button(ask_window, text="ตกลงปริ้น (OK)", font=("Segoe UI", 10, "bold"), bg=COLOR_WARNING, fg="black", width=15, command=confirm)
        btn_ok.pack(pady=10)
        
        self.root.wait_window(ask_window)
        
        if not self.reprint_numbers: return 

        file_path = filedialog.asksaveasfilename(
            title="บันทึกไฟล์ PDF ปริ้นซ่อม",
            defaultextension=".pdf",
            filetypes=[("PDF Files", "*.pdf")],
            initialfile=f"Reprint_{primary_barcode}_Custom.pdf"
        )
        if not file_path: return

        try:
            # 🌟 ปรับลดความสูงของหน้า PDF ซ่อมให้เหลือ 11 cm เพื่อให้ตรงกัน
            page_w, page_h = 10.0 * cm, 11.0 * cm  
            margin_x, margin_y = 0.4 * cm, 0.2 * cm  
            gap_x, gap_y = 0.4 * cm, 0.2 * cm     
            sticker_w = (page_w - (2 * margin_x) - gap_x) / 2
            sticker_h = 1.9 * cm 
            
            # 🌟 ปรับจำนวนแถวเป็น 5 แถว (10 ดวง)
            max_cols, max_rows = 2, 5         
            
            c = canvas.Canvas(file_path, pagesize=(page_w, page_h))
            c.setViewerPreference('PrintScaling', 'None')

            col_idx, row_idx, total_labels = 0, 0, 0
            bc_height = 0.8 * cm
            
            for current_serial in self.reprint_numbers:
                cell_x = margin_x + (col_idx * (sticker_w + gap_x))
                cell_y = page_h - margin_y - sticker_h - (row_idx * (sticker_h + gap_y))

                current_barcode = f"{primary_barcode}-{current_serial:02d}"
                barcode_text = current_barcode.upper()
                
                offset_x = 0.4 * cm if col_idx == 0 else -0.2 * cm
                offset_y = 0.7 * cm if row_idx < 5 else 0

                barcode_obj = code128.Code128(barcode_text, barHeight=bc_height, barWidth=0.5)
                real_bc_width = barcode_obj.width
                
                x_pos = cell_x + (sticker_w - real_bc_width) / 2 + offset_x
                y_pos = cell_y + 4 * mm + offset_y

                barcode_obj.drawOn(c, x_pos, y_pos)

                c.saveState()
                c.setFillColorRGB(0, 0, 0)
                c.setFont("Helvetica", 9)  
                hr_width = c.stringWidth(barcode_text, "Helvetica", 9)
                c.drawString(cell_x + (sticker_w - hr_width) / 2 + offset_x, cell_y + 1.5 * mm + offset_y, barcode_text)
                c.restoreState()
                
                col_idx += 1
                total_labels += 1
                if col_idx >= max_cols:
                    col_idx = 0
                    row_idx += 1
                    if row_idx >= max_rows:
                        c.showPage()
                        col_idx, row_idx = 0, 0
            
            if total_labels > 0:
                c.save()
                messagebox.showinfo("สำเร็จ", f"สร้างไฟล์ PDF ปริ้นซ่อมแบบ 1D เรียบร้อย!\nจำนวนที่ปริ้น: {total_labels} ดวง\n(เลขรันในระบบหลักจะไม่ถูกขยับ)")
                try: os.startfile(file_path)
                except: pass
        except Exception as e:
            messagebox.showerror("Error", f"เกิดข้อผิดพลาดในการสร้าง PDF:\n{str(e)}")

    # --- Tab 6: PDF BEST ---
    def setup_tab_pdf_best(self):
        top = tk.Frame(self.tab_pdf_best, bg=COLOR_BG, pady=10, padx=10); top.pack(fill="x")
        ttk.Button(top, text="📂 เลือกไฟล์ PDF (Best)", style="App.TButton", command=self.browse_pdf_best).pack(side="left", padx=5)
        self.lbl_pdf_status = tk.Label(top, text="Waiting...", font=FONT_MAIN, bg=COLOR_BG)
        self.lbl_pdf_status.pack(side="left", padx=10)
        self.btn_pdf_save = ttk.Button(top, text="💾 บันทึกลง Database (Tab 3)", style="App.TButton", command=self.save_pdf_best_to_db, state="disabled")
        self.btn_pdf_save.pack(side="right", padx=5)
        cols = ("Tracking", "Customer", "Details", "Page")
        self.pdf_tree = ttk.Treeview(self.tab_pdf_best, columns=cols, show="headings")
        self.pdf_tree.heading("Tracking", text="Tracking (Key)"); self.pdf_tree.heading("Customer", text="Customer")
        self.pdf_tree.heading("Details", text="Details (Clean)"); self.pdf_tree.heading("Page", text="Page")
        self.pdf_tree.column("Tracking", width=150); self.pdf_tree.column("Customer", width=200)
        self.pdf_tree.column("Details", width=500); self.pdf_tree.column("Page", width=50, anchor="center")
        vsb = ttk.Scrollbar(self.tab_pdf_best, orient="vertical", command=self.pdf_tree.yview)
        self.pdf_tree.configure(yscrollcommand=vsb.set)
        self.pdf_tree.pack(side="left", fill="both", expand=True); vsb.pack(side="right", fill="y")
        self.add_tree_copy_paste(self.pdf_tree)

    def clean_thai(self, text):
        if not text: return ""
        text = re.sub(r'([ก-๙])\s+([ก-๙])', r'\1\2', text)
        text = re.sub(r'\s+([ะ-ูเ-ไ])', r'\1', text)
        return text

    def extract_pdf_best(self, pdf_path):
        extracted = []
        with pdfplumber.open(pdf_path) as pdf:
            for i, page in enumerate(pdf.pages):
                text = page.extract_text();
                if not text: continue
                lines = [line for line in text.split('\n') if line.strip()]
                cust_name = "N/A"; target_order = "N/A"; notes_text = ""
                ref_top = "N/A"
                if len(lines) > 0:
                    clean = lines[0].strip()
                    if "-" in clean and any(c.isalpha() for c in clean): ref_top = clean
                if len(lines) > 1: cust_name = lines[1].strip().replace("ผู้รับ", "").strip()
                full_text = text.replace(" ", "").replace("\n", "")
                match = re.search(r'(6685\d{8,15})', full_text)
                if match: target_order = match.group(1)
                note_words = page.search(r"หมายเหต")
                if note_words:
                    bbox = note_words[0]
                    sign_words = page.search(r"(เซ็น|เซน|เช็น).*%s(ชื่อ|ชือ)")
                    btm = sign_words[0]['top'] if sign_words else page.height
                    try:
                        area = page.crop((0, bbox['top'], page.width, btm))
                        raw = area.extract_text() or ""
                        clean = raw.replace("\n", "").replace("$", "")
                        clean = re.sub(r'^.*?(หมายเหตุ|หมายเหต)[:.\sุ]*', '', clean).strip()
                        clean = re.sub(r'(เซ็น|เซน|เช็น).*?(ชื่อ|ชือ|ชอื).*$', '', clean).strip()
                        notes_text = self.clean_thai(clean)
                    except: pass
                extracted.append({"Ref": ref_top, "Tracking": target_order, "Customer": cust_name, "Details": notes_text, "Page": i+1})
        return extracted

    def browse_pdf_best(self):
        files = filedialog.askopenfilenames(filetypes=[("PDF", "*.pdf")])
        if not files: return
        self.pdf_tree.delete(*self.pdf_tree.get_children())
        all_data = []
        for f in files:
            try: all_data.extend(self.extract_pdf_best(f))
            except: pass
        for r in all_data:
            self.pdf_tree.insert("", "end", values=(r["Tracking"], r["Customer"], r["Details"], r["Page"]))
        self.pdf_current_df = pd.DataFrame(all_data)
        self.lbl_pdf_status.config(text=f"Loaded {len(all_data)} items", fg="green")
        self.btn_pdf_save.config(state="normal")

    def save_pdf_best_to_db(self):
        if self.pdf_current_df is None or self.pdf_current_df.empty: return
        if not messagebox.askyesno("Confirm", "Save to Database?"): return
        
        inserted_count = 0
        updated_count = 0
        current_date_str = datetime.now().strftime("%d/%m/%Y")
        
        try:
            for _, row in self.pdf_current_df.iterrows():
                key = row['Tracking']
                if key == "N/A": continue
                
                raw_details = str(row['Details']).replace("$", "")
                items = raw_details.replace("+", ",").split(",")
                total_qty = 0
                processed_items = []
                
                for it in items:
                    clean = it.strip()
                    if clean:
                        qty = 1
                        m_eq = re.search(r'=(\d+)', clean)
                        m_unit = re.search(r'(?<!\d)(\d+)\s*(ขวด|ข\.|ซอง|ชิ้น|ก\.|kg|ใบ|กระป๋อง|กป\.|กล่อง|ลัง)', clean, re.IGNORECASE)
                        
                        if m_eq:
                            qty = int(m_eq.group(1))
                        elif m_unit:
                            qty = int(m_unit.group(1))
                            
                        total_qty += qty
                        processed_items.append((clean, qty))

                self.cursor.execute("SELECT number FROM orders WHERE number=%s", (key,))
                exists = self.cursor.fetchone()
                
                if exists:
                    self.cursor.execute("""
                        UPDATE orders 
                        SET customername=%s, order_details=%s, total_qty=%s
                        WHERE number=%s
                    """, (row['Customer'], raw_details, total_qty, key))
                    
                    self.cursor.execute("DELETE FROM order_items WHERE order_number=%s", (key,))
                    for item_name, item_qty in processed_items:
                        self.cursor.execute("INSERT INTO order_items (order_number, sku, name, quantity) VALUES (%s,%s,%s,%s)",
                                    (key, item_name, item_name, item_qty))
                    updated_count += 1
                else:
                    self.cursor.execute("""
                        INSERT INTO orders (number, orderdate, customername, amount, status, shipping_channel, tracking_no, order_details, total_qty)
                        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                    """, (key, current_date_str, row['Customer'], 0.0, "PENDING", "Best", key, raw_details, total_qty))
                    
                    for item_name, item_qty in processed_items:
                        self.cursor.execute("INSERT INTO order_items (order_number, sku, name, quantity) VALUES (%s,%s,%s,%s)",
                                    (key, item_name, item_name, item_qty))
                    inserted_count += 1
                    
            self.conn.commit()
            msg = f"เสร็จสิ้น!\n- เพิ่มออเดอร์ใหม่: {inserted_count} รายการ\n- อัปเดตข้อมูลเดิม: {updated_count} รายการ"
            messagebox.showinfo("Result", msg)
            
            self.load_all_data()
            self.pdf_tree.delete(*self.pdf_tree.get_children())
            self.btn_pdf_save.config(state="disabled")
            
            # --- [NEW] สั่งให้ Tab 5 อัปเดตตัวเองอัตโนมัติ ---
            self.load_barcode_data()
            
        except Exception as e:
            self.conn.rollback()
            messagebox.showerror("Error", str(e))
    # ==========================================
    # --- Tab 7: สรุปยอดค้างส่ง (Pending) ---
    # ==========================================
    # ==========================================
    # --- Tab 7: สรุปยอดค้างส่ง (Pending) ---
    # ==========================================
    # ==========================================
    # --- Tab 7: สรุปยอดค้างส่ง (Pending) ---
    # ==========================================
    # ==========================================
    # --- Tab 7: สรุปยอดค้างส่ง (Pending) ---
    # ==========================================
    # ==========================================
    # --- Tab 7: สรุปยอดค้างส่ง (Pending) ---
    # ==========================================
    def setup_tab_pending(self):
        # --- 1. แถบปุ่มจัดการด้านบน ---
        top_frame = tk.Frame(self.tab_pending, bg=COLOR_WHITE, pady=10)
        top_frame.pack(fill="x")
        
        tk.Label(top_frame, text="📋 รายการออเดอร์ค้างส่ง (PENDING)", font=FONT_HEADER, bg=COLOR_WHITE, fg=COLOR_DANGER).pack(side="left", padx=20)
        
        ttk.Button(top_frame, text="🔄 รีเฟรช", style="App.TButton", command=self.load_pending_orders).pack(side="right", padx=(5, 20))
        ttk.Button(top_frame, text="🗑️ ลบทั้งหมด", style="Danger.TButton", command=self.delete_all_pending).pack(side="right", padx=5)
        ttk.Button(top_frame, text="❌ ลบที่เลือก", style="Danger.TButton", command=self.delete_selected_pending).pack(side="right", padx=5)
        ttk.Button(top_frame, text="📊 สรุปยอดสินค้า", style="App.TButton", command=self.show_pending_summary).pack(side="right", padx=5)

        # --- 🌟 2. แถบค้นหา (Search Bar) เพิ่มใหม่ ---
        search_frame = tk.Frame(self.tab_pending, bg=COLOR_WHITE)
        search_frame.pack(fill="x", padx=20, pady=(0, 10))

        tk.Label(search_frame, text="🔍 ค้นหา (เลขออเดอร์ / เลขพัสดุ):", font=("Segoe UI", 11), bg=COLOR_WHITE).pack(side="left", padx=(0, 5))
        
        self.search_var = tk.StringVar()
        self.search_entry = ttk.Entry(search_frame, textvariable=self.search_var, width=35, font=("Segoe UI", 11))
        self.search_entry.pack(side="left", padx=5)
        
        # กด Enter เพื่อค้นหาได้เลย
        self.search_entry.bind("<Return>", lambda event: self.search_pending())
        
        ttk.Button(search_frame, text="ค้นหา", command=self.search_pending).pack(side="left", padx=5)
        ttk.Button(search_frame, text="ล้างค่า/ดูทั้งหมด", command=self.clear_search_pending).pack(side="left", padx=5)

        # --- 3. ส่วนตารางข้อมูล ---
        tree_container = tk.Frame(self.tab_pending, bg=COLOR_WHITE)
        tree_container.pack(side="top", fill="both", expand=True, padx=10, pady=5)

        cols = ("date", "order", "tracking", "product", "details")
        self.pending_tree = ttk.Treeview(tree_container, columns=cols, show="headings")
        
        def sort_column(tree, col, reverse):
            l = [(tree.set(k, col), k) for k in tree.get_children('')]
            l.sort(reverse=reverse)
            for index, (val, k) in enumerate(l):
                tree.move(k, '', index)
            tree.heading(col, command=lambda: sort_column(tree, col, not reverse))

        headings = [
            ("date", "วันที่นำเข้า"), 
            ("order", "เลขออเดอร์"), 
            ("tracking", "เลขพัสดุ (Tracking)"), 
            ("product", "รายละเอียดสินค้า (ดึงจาก Tab 3)"), 
            ("details", "ช่องทาง")
        ]
        
        for col, text in headings:
            self.pending_tree.heading(col, text=text, command=lambda c=col: sort_column(self.pending_tree, c, False))

        self.pending_tree.column("date", width=120, anchor="center")
        self.pending_tree.column("order", width=170, anchor="center")
        self.pending_tree.column("tracking", width=180, anchor="center")
        self.pending_tree.column("product", width=380, anchor="w") 
        self.pending_tree.column("details", width=100, anchor="center")
        
        vsb = ttk.Scrollbar(tree_container, orient="vertical", command=self.pending_tree.yview)
        self.pending_tree.configure(yscrollcommand=vsb.set)
        self.pending_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y") 

        # --- 4. ส่วนสรุปยอด (Footer) ---
        self.pending_footer = tk.Frame(self.tab_pending, bg="#2c3e50", pady=10)
        self.pending_footer.pack(fill="x")
        self.lbl_pending_summary = tk.Label(self.pending_footer, 
                                            text="สรุปยอดค้าง: รวม 0 | Shopee: 0 | Lazada: 0 | Best: 0", 
                                            font=("Segoe UI", 14, "bold"), bg="#2c3e50", fg="white")
        self.lbl_pending_summary.pack()

        # --- 🌟 5. ระบบคลิกขวา Copy แบบเลือกระดับช่อง (Cell) หรือแถว (Row) ---
        self.p_menu = tk.Menu(self.pending_tree, tearoff=0)
        self.p_menu.add_command(label="📄 คัดลอกเฉพาะข้อมูลช่องนี้ (Copy Cell)", command=self.copy_pending_cell)
        self.p_menu.add_separator()
        self.p_menu.add_command(label="📋 คัดลอกข้อมูลทั้งแถว (Copy Row)", command=self.copy_pending_row)

        def show_context_menu(event):
            # ตรวจสอบว่าคลิกโดนแถวไหน และคอลัมน์ไหน
            item = self.pending_tree.identify_row(event.y)
            column = self.pending_tree.identify_column(event.x)
            
            if item:
                self.pending_tree.selection_set(item) # เลือกแถวนั้นอัตโนมัติ
                self.clicked_item = item
                # แปลงรหัสคอลัมน์ เช่น '#3' ให้กลายเป็น index ตัวเลข 2
                self.clicked_column = int(column.replace('#', '')) - 1 
                
                self.p_menu.post(event.x_root, event.y_root)

        self.pending_tree.bind("<Button-3>", show_context_menu)
        self.pending_tree.bind("<Control-c>", lambda e: self.copy_pending_row())

        # --- 🌟 6. ส่วนโหลดข้อมูลและตั้งเวลา (ต้องอยู่ล่างสุดเสมอ) 🌟 ---
        self.load_pending_orders()
        self.root.after(300000, self.auto_refresh_pending)

    # ==========================================
    # ฟังก์ชันเสริมสำหรับการค้นหาและคัดลอก
    # ==========================================
    def search_pending(self):
        keyword = self.search_var.get().strip()
        self.load_pending_orders(search_keyword=keyword)

    def clear_search_pending(self):
        self.search_var.set("")
        self.load_pending_orders()

    def copy_pending_cell(self):
        """ คัดลอกเฉพาะข้อความในช่องที่คลิกขวา """
        if hasattr(self, 'clicked_item') and hasattr(self, 'clicked_column'):
            try:
                values = self.pending_tree.item(self.clicked_item, "values")
                cell_value = values[self.clicked_column]
                self.root.clipboard_clear()
                self.root.clipboard_append(str(cell_value))
            except Exception as e:
                print(f"Copy Cell Error: {e}")

    def copy_pending_row(self):
        """ คัดลอกข้อมูลทั้งแถว (คั่นด้วย Tab เพื่อไปวางใน Excel ได้) """
        sel = self.pending_tree.selection()
        if not sel: return
        data = []
        for i in sel:
            data.append("\t".join(map(str, self.pending_tree.item(i, "values"))))
        self.root.clipboard_clear()
        self.root.clipboard_append("\n".join(data))

    # ==========================================
    # ฟังก์ชันดึงและจัดการข้อมูล
    # ==========================================
    def load_pending_orders(self, search_keyword=""):
        for i in self.pending_tree.get_children(): self.pending_tree.delete(i)
        try:
            try:
                self.conn.ping(reconnect=True, attempts=3, delay=2)
                self.cursor = self.conn.cursor() 
            except: pass

            self.conn.commit() 
            
            # 🌟 ถ้ามีคำค้นหา ให้เติมเงื่อนไข WHERE LIKE เข้าไป
            if search_keyword:
                query = """
                    SELECT 
                        p.import_date, 
                        p.order_no, 
                        p.tracking_no, 
                        IFNULL(
                            (SELECT GROUP_CONCAT(DISTINCT o.order_details SEPARATOR ' + ') 
                             FROM orders o 
                             WHERE o.number = p.order_no OR o.tracking_no = p.tracking_no), 
                            '- รออิมพอร์ตข้อมูลจาก ZORT -'
                        ) AS product_info,
                        p.shipping_channel 
                    FROM pdf_pending_orders p
                    WHERE p.status = 'PENDING' AND (p.order_no LIKE %s OR p.tracking_no LIKE %s)
                    ORDER BY p.import_date DESC
                """
                like_term = f"%{search_keyword}%"
                self.cursor.execute(query, (like_term, like_term))
            else:
                # ดึงปกติ (ถ้าไม่ได้ค้นหา)
                query = """
                    SELECT 
                        p.import_date, 
                        p.order_no, 
                        p.tracking_no, 
                        IFNULL(
                            (SELECT GROUP_CONCAT(DISTINCT o.order_details SEPARATOR ' + ') 
                             FROM orders o 
                             WHERE o.number = p.order_no OR o.tracking_no = p.tracking_no), 
                            '- รออิมพอร์ตข้อมูลจาก ZORT -'
                        ) AS product_info,
                        p.shipping_channel 
                    FROM pdf_pending_orders p
                    WHERE p.status = 'PENDING'
                    ORDER BY p.import_date DESC
                """
                self.cursor.execute(query)

            rows = self.cursor.fetchall()
            
            s_count = l_count = b_count = 0
            for r in rows:
                self.pending_tree.insert("", "end", values=r)
                note = str(r[4]).upper()
                if "SHOPEE" in note: s_count += 1
                elif "LAZADA" in note: l_count += 1
                elif "BEST" in note: b_count += 1
            
            self.lbl_pending_summary.config(
                text=f"📊 สรุปยอดค้างส่ง:  รวม {len(rows)} กล่อง  |  Shopee: {s_count}  |  Lazada: {l_count}  |  Best: {b_count}"
            )
        except Exception as e:
            self.lbl_pending_summary.config(text=f"🔴 Error: {e} (กำลังพยายามต่อใหม่...)")
    def auto_refresh_pending(self):
        """ ฟังก์ชันสั่งรัน Refresh อัตโนมัติ (ทำหน้าที่โหลดข้อมูลใหม่ แล้วตั้งเวลาตัวเองซ้ำ) """
        try:
            # สั่งให้ดึงข้อมูลใหม่
            self.load_pending_orders()
            
            # ตั้งเวลาให้รันตัวเองอีกครั้งในอีก 5 นาที (300,000 มิลลิวินาที)
            self.root.after(300000, self.auto_refresh_pending)
            
            from datetime import datetime
            print("Tab 7: Auto Refreshed at", datetime.now().strftime('%H:%M:%S'))
        except:
            pass

    def show_pending_summary(self):
        summary = {}
        for child in self.pending_tree.get_children():
            product_str = self.pending_tree.item(child, "values")[3]
            
            if product_str and product_str != '- รออิมพอร์ตข้อมูลจาก ZORT -':
                clean_str = product_str.replace(' + ', ', ')
                items = [x.strip() for x in clean_str.split(', ')]
                
                for item in items:
                    if item:
                        summary[item] = summary.get(item, 0) + 1

        if not summary:
            from tkinter import messagebox
            messagebox.showinfo("แจ้งเตือน", "ไม่มีข้อมูลสินค้าให้สรุปยอด\n(ออเดอร์อาจจะยังไม่ได้อิมพอร์ตข้อมูลจาก ZORT)")
            return

        top = tk.Toplevel(self.root)
        top.title("📊 สรุปยอดสินค้าค้างส่ง (เทียบสต็อก)")
        top.geometry("780x480") 
        try: top.configure(bg=COLOR_WHITE)
        except: top.configure(bg="white")

        tk.Label(top, text="📦 สรุปจำนวนสินค้าที่ต้องเตรียมแพ็ค เทียบกับสต็อกคงเหลือ", font=("Segoe UI", 16, "bold"), bg="white", fg="#2c3e50").pack(pady=(15, 5))
        tk.Label(top, text="(แถวสีแดง = สต็อกไม่พอแพ็ค ต้องเร่งทำเพิ่ม)", font=("Segoe UI", 10), bg="white", fg="red").pack(pady=(0, 10))

        tree_frame = tk.Frame(top, bg="white")
        tree_frame.pack(fill="both", expand=True, padx=20, pady=5)

        cols = ("product", "qty", "stock")
        sum_tree = ttk.Treeview(tree_frame, columns=cols, show="headings", height=12)
        sum_tree.heading("product", text="รายการสินค้า (จัดกลุ่มแยกชิ้นแล้ว)")
        sum_tree.heading("qty", text="จำนวน (ออเดอร์)")
        sum_tree.heading("stock", text="สต็อกคงเหลือ (เทียบเป็นกล่อง)")
        
        sum_tree.column("product", width=450, anchor="w")
        sum_tree.column("qty", width=120, anchor="center")
        sum_tree.column("stock", width=150, anchor="center")

        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=sum_tree.yview)
        sum_tree.configure(yscrollcommand=vsb.set)
        sum_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        sum_tree.tag_configure("low_stock", foreground="#b00000", background="#ffe6e6")
        sum_tree.tag_configure("normal", foreground="black", background="white")

        sorted_summary = sorted(summary.items(), key=lambda x: x[1], reverse=True)
        total_qty = 0
        
        import re 
        
        for item_name, qty in sorted_summary:
            stock_qty = 0
            target_sku = ""
            try:
                self.cursor.execute("SELECT quantity FROM stock WHERE sku=%s", (item_name,))
                res = self.cursor.fetchone()
                
                if res:
                    stock_qty = res[0]
                    target_sku = item_name
                else:
                    self.cursor.execute("SELECT barcode FROM product_barcode_alias WHERE alias=%s", (item_name,))
                    bc_res = self.cursor.fetchone()
                    if bc_res:
                        barcode = bc_res[0]
                        self.cursor.execute("SELECT stock_sku, base_name FROM product_barcodes WHERE barcode=%s", (barcode,))
                        cfg = self.cursor.fetchone()
                        if cfg:
                            target_sku = cfg[0] if (cfg[0] and str(cfg[0]).strip() != "None" and str(cfg[0]).strip() != "") else cfg[1]
                            self.cursor.execute("SELECT quantity FROM stock WHERE sku=%s", (target_sku,))
                            res2 = self.cursor.fetchone()
                            if res2:
                                stock_qty = res2[0]
            except:
                pass

            if stock_qty is not None:
                # 🌟 ยก Logic การหารกล่องจาก Tab 1 มาใช้แบบ 100% 🌟
                divisor = 1
                check_sku = target_sku if target_sku else item_name
                
                m_sku = re.findall(r'_(\d+)', str(check_sku))
                if m_sku:
                    divisor = int(m_sku[-1])
                elif "DUO SET" in str(check_sku).upper():
                    divisor = 2
                    
                if divisor > 1:
                    stock_qty = stock_qty / divisor

                display_stock = int(stock_qty) if float(stock_qty).is_integer() else round(stock_qty, 2)
            else:
                display_stock = 0

            row_tag = "normal"
            if display_stock < qty:
                row_tag = "low_stock"

            sum_tree.insert("", "end", values=(item_name, f"{qty} รายการ", f"{display_stock}"), tags=(row_tag,))
            total_qty += qty

        footer = tk.Frame(top, bg="#e74c3c", pady=10)
        footer.pack(fill="x", side="bottom")
        tk.Label(footer, text=f"รวมทั้งหมด: {total_qty} รายการ", font=("Segoe UI", 14, "bold"), bg="#e74c3c", fg="white").pack()

    def delete_selected_pending(self):
        from tkinter import messagebox
        items = self.pending_tree.selection()
        if not items: return
        if messagebox.askyesno("ยืนยัน", f"ลบ {len(items)} รายการที่เลือกใช่หรือไม่?"):
            for i in items:
                oid = self.pending_tree.item(i, "values")[1]
                self.cursor.execute("DELETE FROM pdf_pending_orders WHERE order_no=%s", (oid,))
            self.conn.commit()
            self.load_pending_orders()

    def delete_all_pending(self):
        from tkinter import messagebox
        if messagebox.askyesno("ยืนยันขั้นเด็ดขาด", "คุณต้องการล้างรายการค้างส่ง 'ทั้งหมด' ใช่หรือไม่?"):
            self.cursor.execute("DELETE FROM pdf_pending_orders WHERE status = 'PENDING'")
            self.conn.commit()
            self.load_pending_orders()

if __name__ == "__main__":
    root = tk.Tk()
    app = ZortWMSApp(root)
    root.mainloop()