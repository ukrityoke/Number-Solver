"""
โปรแกรมหาสูตรคำนวณจากตัวเลข 4-5 ตัว ให้ได้คำตอบตามที่กำหนด
==========================================================
- รองรับเครื่องหมาย: + - * / ^ (ยกกำลัง) ! (แฟกทอเรียล) % (มอดูโล) √ (รากที่ 2) ∛ (รากที่ 3) และวงเล็บ (โดยอัตโนมัติ)
- มีเครื่องหมายเสริมให้เลือกเพิ่ม: // (หารปัดเศษลง)
- เลือกได้ว่าจะอนุญาตให้ใช้ตัวเลขซ้ำหรือไม่ (ค่าเริ่มต้น = ไม่ซ้ำ คือใช้เลขที่กรอกแต่ละตัวครั้งเดียว)
- เลือกได้ว่าจะ "บังคับ" ให้คำตอบต้องมีเครื่องหมายใดบ้าง (เช่น บังคับต้องมี ! หรือบังคับต้องมี %)
- ใช้เลขคณิตแบบเศษส่วน (Fraction) ตลอดการคำนวณ เพื่อความแม่นยำ 100% ไม่มีปัญหาความคลาดเคลื่อนของทศนิยม
  (√ และ ∛ จะใช้ได้ก็ต่อเมื่อผลลัพธ์ออกมาเป็นเศษส่วน/จำนวนเต็มพอดี เพื่อรักษาความแม่นยำแบบ 100% เสมอ)
- ใช้เทคนิค memoization (จดจำสถานะที่เคยลองแล้ว) เพื่อตัดกิ่งการค้นหาที่ซ้ำซ้อน ทำให้ค้นหาได้เร็วขึ้นมาก
  และหยุดทันทีเมื่อเจอคำตอบแรก (early stopping)
- เมื่อเจอคำตอบ จะแสดง "วิธีทำทีละขั้น" ด้านล่าง เพื่อให้ตรวจสอบความถูกต้องได้ง่าย
- เมื่อสูตรมีวงเล็บซ้อนกันหลายชั้น จะสลับชนิดวงเล็บตามความลึก () -> [] -> {} -> () ... เพื่อให้อ่านง่าย

หากต้องการเพิ่มเครื่องหมายใหม่ ๆ ในอนาคต ให้ไปแก้ที่ฟังก์ชัน gen_pair_results() และ build_variants()
"""

import math
import itertools
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox
from fractions import Fraction

# ---------------------------------------------------------------------------
# ส่วนตรรกะการคำนวณ (ไม่เกี่ยวกับ UI)
# ---------------------------------------------------------------------------

MAX_FACTORIAL_INPUT = 10   # จำกัดแฟกทอเรียลไม่ให้ตัวเลขใหญ่เกินไปจนช้า/ไม่มีประโยชน์
MAX_POWER_EXP = 6          # จำกัดเลขชี้กำลังไม่ให้ตัวเลขระเบิดใหญ่เกินไป

# เครื่องหมายที่แสดงผลให้สวยขึ้นตอนโชว์ขั้นตอน (ของจริงตอนคำนวณยังใช้สัญลักษณ์เดิม)
DISPLAY_SYMBOL = {'+': '+', '-': '-', '*': '×', '/': '÷', '//': 'div', '^': '^', '%': 'mod'}

# เครื่องหมายยูนารี (ทำกับเลขตัวเดียว): เก็บว่าเป็นแบบ "postfix" (ต่อท้าย เช่น 4!) หรือ
# "prefix" (นำหน้า เช่น √16) และสัญลักษณ์ที่ใช้แสดงผล
UNARY_DISPLAY = {
    '!': ('post', '!'),
    'sqrt': ('pre', '√'),
    'cbrt': ('pre', '∛'),
}

# ชนิดวงเล็บที่จะสลับใช้ตามความลึกของการซ้อน เพื่อให้อ่านสูตรที่ซับซ้อนได้ง่ายขึ้น
BRACKET_TYPES = [('(', ')'), ('[', ']'), ('{', '}')]


def bracket_pair(depth: int):
    return BRACKET_TYPES[depth % len(BRACKET_TYPES)]


def integer_nth_root(n: int, k: int):
    """คืนค่าจำนวนเต็ม r ที่ r**k == n พอดี (หรือ None ถ้าไม่มีจำนวนเต็มที่ลงตัว)
    รองรับ n ติดลบเมื่อ k เป็นเลขคี่ (เช่นรากที่ 3 ของจำนวนลบ)"""
    if n < 0:
        if k % 2 == 0:
            return None
        r = integer_nth_root(-n, k)
        return -r if r is not None else None
    if n == 0:
        return 0
    lo, hi = 0, 1
    while hi ** k <= n:
        hi *= 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** k <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo if lo ** k == n else None


def try_root(value: Fraction, k: int):
    """หารากที่ k ของเศษส่วน ถ้าลงตัวพอดีทั้งเศษและส่วน คืนค่า Fraction ผลลัพธ์ ไม่งั้นคืน None"""
    rn = integer_nth_root(value.numerator, k)
    if rn is None:
        return None
    rd = integer_nth_root(value.denominator, k)
    if rd is None:
        return None
    return Fraction(rn, rd)


class SolutionFound(Exception):
    """ใช้เพื่อ 'โยน' คำตอบ (โหนดของต้นไม้นิพจน์) ออกจากการค้นหาทันทีที่เจอ"""
    def __init__(self, node):
        self.node = node


def format_num(v: Fraction) -> str:
    if v.denominator == 1:
        return str(v.numerator)
    return f"{v.numerator}/{v.denominator}"


# ---- โครงสร้างต้นไม้ของนิพจน์ ----------------------------------------------
# leaf  : ('L', value)
# op    : ('OP', symbol, left_node, right_node, value)
# unary : ('U', symbol, child_node, value)   -- symbol เป็นหนึ่งใน '!', 'sqrt', 'cbrt'

def node_value(node) -> Fraction:
    if node[0] == 'L':
        return node[1]
    if node[0] == 'OP':
        return node[4]
    return node[3]  # 'U'


def collect_ops(node, acc: set):
    if node[0] == 'L':
        return
    if node[0] == 'OP':
        acc.add(node[1])
        collect_ops(node[2], acc)
        collect_ops(node[3], acc)
    else:  # 'U'
        acc.add(node[1])
        collect_ops(node[2], acc)


def to_infix(node, depth: int = 0) -> str:
    """แปลงต้นไม้เป็นข้อความสูตร โดยสลับชนิดวงเล็บตามความลึกของการซ้อน: () -> [] -> {} -> () ..."""
    if node[0] == 'L':
        return format_num(node[1])
    ob, cb = bracket_pair(depth)
    if node[0] == 'OP':
        left = to_infix(node[2], depth + 1)
        right = to_infix(node[3], depth + 1)
        return f"{ob}{left} {node[1]} {right}{cb}"
    # 'U'
    kind, disp = UNARY_DISPLAY[node[1]]
    child = to_infix(node[2], depth + 1)
    if kind == 'post':
        return f"{ob}{child}{cb}{disp}"
    return f"{disp}{ob}{child}{cb}"


def to_steps(node, steps: list):
    """เดินต้นไม้แบบ post-order สร้างรายการขั้นตอนคำนวณทีละขั้น (สั้น ๆ ตรวจง่าย)"""
    if node[0] == 'L':
        return
    if node[0] == 'OP':
        to_steps(node[2], steps)
        to_steps(node[3], steps)
        lv, rv, val = node_value(node[2]), node_value(node[3]), node[4]
        sym = DISPLAY_SYMBOL.get(node[1], node[1])
        steps.append(f"{format_num(lv)} {sym} {format_num(rv)} = {format_num(val)}")
    else:  # 'U'
        to_steps(node[2], steps)
        kind, disp = UNARY_DISPLAY[node[1]]
        cv, val = node_value(node[2]), node[3]
        if kind == 'post':
            steps.append(f"{format_num(cv)}{disp} = {format_num(val)}")
        else:
            steps.append(f"{disp}{format_num(cv)} = {format_num(val)}")


def try_unary_node(node, symbol: str):
    """ลองสร้างโหนดยูนารีจากโหนดหนึ่ง: '!' แฟกทอเรียล, 'sqrt' รากที่ 2, 'cbrt' รากที่ 3
    คืน None ถ้าทำไม่ได้ (เช่น ไม่ใช่จำนวนเต็มที่เหมาะสม หรือรากไม่ลงตัว)"""
    val = node_value(node)
    if symbol == '!':
        if val.denominator == 1 and 0 <= val.numerator <= MAX_FACTORIAL_INPUT:
            return ('U', '!', node, Fraction(math.factorial(val.numerator)))
        return None
    if symbol == 'sqrt':
        if val < 0:
            return None
        root = try_root(val, 2)
        return ('U', 'sqrt', node, root) if root is not None else None
    if symbol == 'cbrt':
        root = try_root(val, 3)
        return ('U', 'cbrt', node, root) if root is not None else None
    return None


def gen_pair_results(a_node, b_node, ops: set):
    """สร้างโหนดผลลัพธ์ที่เป็นไปได้ทั้งหมด จากการนำ a และ b มาคำนวณกันด้วยเครื่องหมายที่เลือกไว้"""
    a, b = node_value(a_node), node_value(b_node)
    res = []
    if '+' in ops:
        res.append(('OP', '+', a_node, b_node, a + b))
    if '-' in ops:
        res.append(('OP', '-', a_node, b_node, a - b))
    if '*' in ops:
        res.append(('OP', '*', a_node, b_node, a * b))
    if '/' in ops and b != 0:
        res.append(('OP', '/', a_node, b_node, a / b))
    if '//' in ops and b != 0 and a.denominator == 1 and b.denominator == 1:
        res.append(('OP', '//', a_node, b_node, Fraction(a.numerator // b.numerator)))
    if '^' in ops:
        if b.denominator == 1 and abs(b.numerator) <= MAX_POWER_EXP and not (a == 0 and b.numerator < 0):
            try:
                res.append(('OP', '^', a_node, b_node, a ** b.numerator))
            except ZeroDivisionError:
                pass
    if '%' in ops and a.denominator == 1 and b.denominator == 1 and b.numerator != 0:
        res.append(('OP', '%', a_node, b_node, Fraction(a.numerator % b.numerator)))

    extra = []
    for node in res:
        for symbol in ('!', 'sqrt', 'cbrt'):
            if symbol in ops:
                u = try_unary_node(node, symbol)
                if u:
                    extra.append(u)
    res.extend(extra)
    return res


def build_variants(num: Fraction, ops: set):
    """เตรียมตัวเลือกของเลขแต่ละตัวก่อนเริ่มค้นหา
    (ตัวมันเอง, ตัวมันเอง! / √ตัวมันเอง / ∛ตัวมันเอง ถ้าเลือกเครื่องหมายนั้นไว้และทำได้)"""
    leaf = ('L', num)
    variants = [leaf]
    for symbol in ('!', 'sqrt', 'cbrt'):
        if symbol in ops:
            u = try_unary_node(leaf, symbol)
            if u:
                variants.append(u)
    return variants


def solve(nodes, target: Fraction, ops: set, memo: set, stop_flag: threading.Event, required_ops: frozenset):
    """DFS แบบรวมเลขทีละคู่ (สร้างวงเล็บ/ลำดับการคำนวณทุกแบบไปในตัว) พร้อม memo กันซ้ำ"""
    if stop_flag.is_set():
        return
    n = len(nodes)
    if n == 1:
        node = nodes[0]
        if node_value(node) == target:
            if required_ops:
                used = set()
                collect_ops(node, used)
                if not required_ops.issubset(used):
                    return
            raise SolutionFound(node)
        return

    values = tuple(sorted((node_value(nd).numerator, node_value(nd).denominator) for nd in nodes))
    if required_ops:
        used = set()
        for nd in nodes:
            collect_ops(nd, used)
        satisfied = required_ops.issubset(used)
        key = (values, satisfied)
    else:
        key = values
    if key in memo:
        return
    memo.add(key)

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            rest = [nodes[k] for k in range(n) if k != i and k != j]
            for newnode in gen_pair_results(nodes[i], nodes[j], ops):
                solve(rest + [newnode], target, ops, memo, stop_flag, required_ops)


def find_solution(numbers, target: Fraction, ops: set, allow_repeat: bool,
                   stop_flag: threading.Event, required_ops: frozenset = frozenset()):
    """คืนค่าโหนดต้นไม้นิพจน์ของคำตอบที่เจอ (หรือ None ถ้าไม่เจอ)"""
    n = len(numbers)
    if allow_repeat:
        pools = list(itertools.combinations_with_replacement(numbers, n))
    else:
        pools = [tuple(numbers)]

    for pool in pools:
        if stop_flag.is_set():
            return None
        variant_lists = [build_variants(v, ops) for v in pool]
        for combo in itertools.product(*variant_lists):
            if stop_flag.is_set():
                return None
            memo = set()
            try:
                solve(list(combo), target, ops, memo, stop_flag, required_ops)
            except SolutionFound as sf:
                return sf.node
    return None


def parse_fraction(text: str) -> Fraction:
    text = text.strip()
    if not text:
        raise ValueError("ห้ามเว้นว่าง")
    try:
        return Fraction(text)
    except Exception:
        raise ValueError(f"'{text}' ไม่ใช่ตัวเลขที่ถูกต้อง (ใส่จำนวนเต็ม ทศนิยม หรือเศษส่วน เช่น 3/4 ได้)")


# ---------------------------------------------------------------------------
# ส่วน UI (tkinter)
# ---------------------------------------------------------------------------

MAIN_OP_LABELS = {'+': '+ บวก', '-': '- ลบ', '*': '× คูณ', '/': '÷ หาร',
                  '^': '^ ยกกำลัง',
                  'sqrt': '√ รากที่ 2 (สแควร์รูท)',
                  'cbrt': '∛ รากที่ 3 (คิวบ์รูท)',
                  '!': '! แฟกทอเรียล', '%': '% มอดูโล (เศษจากการหาร)'}
EXTRA_OP_LABELS = {'//': '// หารปัดเศษลง (integer division)'}


class SolverApp:
    def __init__(self, root):
        self.root = root
        root.title("โปรแกรมหาสูตรคำนวณตัวเลข")
        root.geometry("700x900")
        root.minsize(700, 760)
        root.resizable(True, True)

        self.stop_flag = threading.Event()
        self.worker_thread = None
        self._found_node = None

        self.count_var = tk.IntVar(value=4)
        self.number_entries = []
        self.target_var = tk.StringVar()
        self.repeat_var = tk.BooleanVar(value=False)  # ค่าเริ่มต้น: ไม่ให้ใช้เลขซ้ำ

        # เครื่องหมายหลัก ค่าเริ่มต้นเลือกหมด ยกเว้น %
        self.op_vars = {
            '+': tk.BooleanVar(value=True),
            '-': tk.BooleanVar(value=True),
            '*': tk.BooleanVar(value=True),
            '/': tk.BooleanVar(value=True),
            '^': tk.BooleanVar(value=True),
            'sqrt': tk.BooleanVar(value=True),
            'cbrt': tk.BooleanVar(value=True),
            '!': tk.BooleanVar(value=True),
            '%': tk.BooleanVar(value=False),
        }
        # เครื่องหมายเสริม (เพิ่มเติมได้ในอนาคต) ค่าเริ่มต้นไม่เลือก
        self.extra_op_vars = {
            '//': tk.BooleanVar(value=False),
        }

        # checkbox "บังคับต้องใช้เครื่องหมายนี้" (ทุกตัว ค่าเริ่มต้นไม่บังคับ)
        self.required_vars = {op: tk.BooleanVar(value=False) for op in
                               list(MAIN_OP_LABELS.keys()) + list(EXTRA_OP_LABELS.keys())}

        self._build_ui()
        self._rebuild_number_entries()

    # ------------------------------------------------------------------
    def _build_ui(self):
        pad = {'padx': 10, 'pady': 6}

        # --- จำนวนตัวเลข ---
        frame_count = ttk.LabelFrame(self.root, text="จำนวนตัวเลขที่ใช้")
        frame_count.pack(fill="x", **pad)
        ttk.Radiobutton(frame_count, text="4 ตัวเลข", variable=self.count_var, value=4,
                         command=self._rebuild_number_entries).pack(side="left", padx=10, pady=5)
        ttk.Radiobutton(frame_count, text="5 ตัวเลข", variable=self.count_var, value=5,
                         command=self._rebuild_number_entries).pack(side="left", padx=10, pady=5)

        # --- ช่องกรอกตัวเลข ---
        self.frame_numbers = ttk.LabelFrame(self.root, text="กรอกตัวเลข")
        self.frame_numbers.pack(fill="x", **pad)

        # --- คำตอบที่ต้องการ ---
        frame_target = ttk.LabelFrame(self.root, text="คำตอบที่ต้องการ")
        frame_target.pack(fill="x", **pad)
        ttk.Entry(frame_target, textvariable=self.target_var, width=20,
                  font=("TH Sarabun New", 14)).pack(padx=10, pady=8, anchor="w")

        # --- เครื่องหมายหลัก + บังคับใช้ (จัดเป็นตาราง 3 คอลัมน์: ชื่อ / อนุญาต / บังคับ) ---
        frame_ops = ttk.LabelFrame(self.root, text="เครื่องหมายที่อนุญาตให้ใช้  /  บังคับต้องใช้")
        frame_ops.pack(fill="x", **pad)

        header = ttk.Frame(frame_ops)
        header.pack(fill="x", padx=10, pady=(6, 0))
        ttk.Label(header, text="เครื่องหมาย", width=26).grid(row=0, column=0, sticky="w")
        ttk.Label(header, text="อนุญาต").grid(row=0, column=1, padx=8)
        ttk.Label(header, text="บังคับต้องมี").grid(row=0, column=2, padx=8)

        all_ops_labels = list(MAIN_OP_LABELS.items()) + list(EXTRA_OP_LABELS.items())
        rows = ttk.Frame(frame_ops)
        rows.pack(fill="x", padx=10, pady=4)
        allow_vars_all = {**self.op_vars, **self.extra_op_vars}
        for i, (op, label) in enumerate(all_ops_labels):
            ttk.Label(rows, text=label, width=26).grid(row=i, column=0, sticky="w", pady=2)
            ttk.Checkbutton(rows, variable=allow_vars_all[op]).grid(row=i, column=1, padx=18)
            ttk.Checkbutton(rows, variable=self.required_vars[op]).grid(row=i, column=2, padx=18)

        note = ttk.Label(frame_ops, foreground="#666",
                          text="(วงเล็บจะถูกใส่ให้อัตโนมัติตามลำดับการคำนวณที่ดีที่สุด และสลับชนิดตามความลึก "
                               "() -> [] -> {} -> () ... เพื่อให้อ่านสูตรที่ซ้อนกันหลายชั้นได้ง่ายขึ้น / "
                               "ติ๊ก 'บังคับต้องมี' = คำตอบที่ได้จะต้องใช้เครื่องหมายนั้นอย่างน้อย 1 ครั้ง / "
                               "√ และ ∛ จะใช้ได้เฉพาะตอนที่ผลลัพธ์ลงตัวพอดีเท่านั้น)",
                          wraplength=640, justify="left")
        note.pack(anchor="w", padx=10, pady=(2, 8))

        # --- ตัวเลือกใช้เลขซ้ำ ---
        frame_repeat = ttk.LabelFrame(self.root, text="การใช้ตัวเลขซ้ำ")
        frame_repeat.pack(fill="x", **pad)
        ttk.Checkbutton(frame_repeat, text="อนุญาตให้ใช้ตัวเลขซ้ำได้ (ค่าเริ่มต้น: ไม่ซ้ำ ใช้แต่ละตัวครั้งเดียว)",
                        variable=self.repeat_var).pack(anchor="w", padx=10, pady=5)

        # --- ปุ่มคำนวณ ---
        frame_btn = ttk.Frame(self.root)
        frame_btn.pack(fill="x", **pad)
        self.calc_btn = ttk.Button(frame_btn, text="🔢 คำนวณ (Calculate)", command=self._on_calculate)
        self.calc_btn.pack(side="left", padx=10)
        self.stop_btn = ttk.Button(frame_btn, text="หยุด", command=self._on_stop, state="disabled")
        self.stop_btn.pack(side="left", padx=10)
        self.status_var = tk.StringVar(value="พร้อมคำนวณ")
        ttk.Label(frame_btn, textvariable=self.status_var, foreground="#0066cc").pack(side="left", padx=10)

        # --- ผลลัพธ์ ---
        frame_result = ttk.LabelFrame(self.root, text="ผลลัพธ์ และวิธีทำ (สำหรับตรวจสอบ)")
        frame_result.pack(fill="both", expand=True, **pad)
        self.result_text = tk.Text(frame_result, height=14, wrap="word", font=("Consolas", 12))
        self.result_text.pack(fill="both", expand=True, padx=8, pady=8)
        self.result_text.configure(state="disabled")

    def _rebuild_number_entries(self):
        for w in self.frame_numbers.winfo_children():
            w.destroy()
        self.number_entries = []
        count = self.count_var.get()
        col_frame = ttk.Frame(self.frame_numbers)
        col_frame.pack(padx=10, pady=8, anchor="w")
        for i in range(count):
            cell = ttk.Frame(col_frame)
            cell.pack(fill="x", pady=5, anchor="w")
            ttk.Label(cell, text=f"เลขตัวที่ {i + 1}:", width=12).pack(side="left", padx=(0, 8))
            e = ttk.Entry(cell, width=14, font=("TH Sarabun New", 13))
            e.pack(side="left")
            self.number_entries.append(e)

    # ------------------------------------------------------------------
    def _set_result(self, text):
        self.result_text.configure(state="normal")
        self.result_text.delete("1.0", "end")
        self.result_text.insert("1.0", text)
        self.result_text.configure(state="disabled")

    def _on_calculate(self):
        # อ่านค่าตัวเลข
        try:
            numbers = [parse_fraction(e.get()) for e in self.number_entries]
            target = parse_fraction(self.target_var.get())
        except ValueError as ex:
            messagebox.showerror("ข้อมูลไม่ถูกต้อง", str(ex))
            return

        ops = {op for op, var in self.op_vars.items() if var.get()}
        ops |= {op for op, var in self.extra_op_vars.items() if var.get()}
        if not ops:
            messagebox.showerror("ไม่ได้เลือกเครื่องหมาย", "กรุณาเลือกเครื่องหมายอย่างน้อย 1 ตัว")
            return

        required_ops = frozenset(op for op, var in self.required_vars.items() if var.get())
        not_allowed_but_required = required_ops - ops
        if not_allowed_but_required:
            names = ", ".join(sorted(not_allowed_but_required))
            messagebox.showerror(
                "เงื่อนไขขัดแย้งกัน",
                f"คุณติ๊ก 'บังคับต้องมี' เครื่องหมาย [{names}] แต่ไม่ได้ติ๊ก 'อนุญาต' เครื่องหมายนี้ไว้\n"
                "กรุณาติ๊กอนุญาตให้ใช้เครื่องหมายนั้นด้วย")
            return

        allow_repeat = self.repeat_var.get()

        self.stop_flag = threading.Event()
        self.calc_btn.configure(state="disabled")
        self.stop_btn.configure(state="normal")
        self.status_var.set("กำลังคำนวณ...")
        self._set_result("")

        self.worker_thread = threading.Thread(
            target=self._run_search, args=(numbers, target, ops, allow_repeat, required_ops), daemon=True
        )
        self.worker_thread.start()
        self._start_time = time.time()
        self.root.after(150, self._poll_thread)

    def _run_search(self, numbers, target, ops, allow_repeat, required_ops):
        self._found_node = find_solution(numbers, target, ops, allow_repeat, self.stop_flag, required_ops)

    def _poll_thread(self):
        if self.worker_thread.is_alive():
            elapsed = time.time() - self._start_time
            self.status_var.set(f"กำลังคำนวณ... ({elapsed:.1f} วินาที)")
            self.root.after(150, self._poll_thread)
            return

        elapsed = time.time() - self._start_time
        self.calc_btn.configure(state="normal")
        self.stop_btn.configure(state="disabled")

        if self.stop_flag.is_set() and self._found_node is None:
            self.status_var.set("หยุดการคำนวณแล้ว")
            self._set_result("ผู้ใช้สั่งหยุดการค้นหาก่อนจะเจอคำตอบ")
            return

        if self._found_node is not None:
            self.status_var.set(f"เจอคำตอบแล้ว! (ใช้เวลา {elapsed:.2f} วินาที)")
            infix = to_infix(self._found_node)
            steps = []
            to_steps(self._found_node, steps)
            lines = [f"สูตรที่ได้:  {infix} = {self.target_var.get()}", ""]
            lines.append("วิธีทำทีละขั้น (ใช้ตรวจสอบความถูกต้อง):")
            for idx, step in enumerate(steps, start=1):
                lines.append(f"  ขั้นที่ {idx}:  {step}")
            lines.append("")
            lines.append(f"ผลลัพธ์สุดท้าย = {format_num(node_value(self._found_node))} "
                          f"({'ตรงกับ' if node_value(self._found_node) == parse_fraction(self.target_var.get()) else 'ไม่ตรงกับ'}"
                          f"คำตอบที่ต้องการ {self.target_var.get()})")
            self._set_result("\n".join(lines))
        else:
            self.status_var.set(f"ค้นหาเสร็จสิ้น ({elapsed:.2f} วินาที)")
            self._set_result("ไม่พบวิธีคำนวณที่ให้คำตอบตรงตามเงื่อนไข/เครื่องหมายที่เลือกไว้\n"
                              "ลองเปลี่ยนเครื่องหมายที่อนุญาต ปิดเงื่อนไข 'บังคับต้องมี' บางตัว "
                              "หรือเปิดตัวเลือก 'ใช้ตัวเลขซ้ำ' ดู")

    def _on_stop(self):
        self.stop_flag.set()
        self.status_var.set("กำลังหยุด...")


if __name__ == "__main__":
    root = tk.Tk()
    app = SolverApp(root)
    root.mainloop()
