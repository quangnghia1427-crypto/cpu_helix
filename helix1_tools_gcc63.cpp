// HELIX-1 - bo cong cu kiem chung (tuong thich GCC 6.3.0 / C++14)
// Bien dich: g++ -std=c++14 -O2 -Wall -Wextra -o helix1_tools helix1_tools_gcc63.cpp
// Chay:      ./helix1_tools
// Ban nay mo phong golden va pipeline, khong can FPGA hay Icarus Verilog.

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace std;

using u32 = uint32_t;
using u64 = uint64_t;

constexpr u64 M64 = numeric_limits<u64>::max();
constexpr u32 M32 = numeric_limits<u32>::max();
constexpr int IWORDS = 128;
constexpr int DWORDS = 32;

const unordered_map<string, int> OPS = {
    {"ADD", 0}, {"SUB", 1}, {"AND", 8}, {"OR", 9}, {"XOR", 10},
    {"SLL", 16}, {"SRL", 17}, {"ADDI", 32}, {"LW", 64},
    {"SW", 80}, {"BEQ", 96}, {"JAL", 121}
};

const unordered_map<int, int> ALU_OF = {
    {0, 0}, {1, 1}, {8, 2}, {9, 3}, {10, 4}, {16, 5}, {17, 6}
};

constexpr u32 HALT = 121; // JAL x0, 0

string trim(const string& s) {
    size_t first = s.find_first_not_of(" \t\r\n");
    if (first == string::npos) return "";
    size_t last = s.find_last_not_of(" \t\r\n");
    return s.substr(first, last - first + 1);
}

// Tra ve gia tri sign-extend duoi dang so nguyen 64-bit khong dau.
u64 sx(u64 value, int bits) {
    const u64 mask = (u64(1) << bits) - 1;
    value &= mask;
    if (value & (u64(1) << (bits - 1))) value |= ~mask;
    return value;
}

u32 fit_imm(int64_t imm, int bits, const string& what) {
    const int64_t lo = -(int64_t(1) << (bits - 1));
    const int64_t hi = (int64_t(1) << (bits - 1)) - 1;
    if (imm < lo || imm > hi) {
        ostringstream msg;
        msg << what << ": imm " << imm << " ngoai [" << lo << "," << hi << "]";
        throw runtime_error(msg.str());
    }
    return static_cast<u32>(static_cast<uint64_t>(imm) & ((u64(1) << bits) - 1));
}

u32 enc_r(int op, int rd, int rs1, int rs2) {
    return (u32(rs2) << 17) | (u32(rs1) << 12) | (u32(rd) << 7) | u32(op);
}
u32 enc_i(int op, int rd, int rs1, int64_t imm) {
    return (fit_imm(imm, 15, "I") << 17) | (u32(rs1) << 12) | (u32(rd) << 7) | u32(op);
}
u32 enc_s(int op, int rs1, int rs2, int64_t imm) {
    return (fit_imm(imm, 10, "S/B") << 22) | (u32(rs2) << 17) | (u32(rs1) << 12) | u32(op);
}
u32 enc_j(int op, int rd, int64_t imm) {
    return (fit_imm(imm, 20, "J") << 12) | (u32(rd) << 7) | u32(op);
}

int64_t parse_integer(const string& token) {
    string t = trim(token);
    if (t.empty()) throw runtime_error("thieu so nguyen");
    size_t used = 0;
    long long value;
    try {
        value = stoll(t, &used, 0);
    } catch (...) {
        throw runtime_error("khong doc duoc so nguyen: " + t);
    }
    if (used != t.size()) throw runtime_error("so nguyen khong hop le: " + t);
    return static_cast<int64_t>(value);
}

vector<string> split_args(const string& s) {
    vector<string> result;
    string part;
    stringstream ss(s);
    while (getline(ss, part, ',')) {
        part = trim(part);
        if (!part.empty()) result.push_back(part);
    }
    return result;
}

vector<u32> assemble(const string& src) {
    unordered_map<string, int> labels;
    vector<string> lines;
    stringstream input(src);
    string raw;

    while (getline(input, raw)) {
        size_t comment = raw.find(';');
        if (comment != string::npos) raw = raw.substr(0, comment);
        string line = trim(raw);
        while (line.find(':') != string::npos) {
            size_t pos = line.find(':');
            string label = trim(line.substr(0, pos));
            if (label.empty()) throw runtime_error("nhan (label) rong");
            labels[label] = static_cast<int>(lines.size());
            line = trim(line.substr(pos + 1));
        }
        if (!line.empty()) lines.push_back(line);
    }

    auto reg = [](const string& token) -> int {
        string t = token;
        transform(t.begin(), t.end(), t.begin(), [](unsigned char c) { return char(tolower(c)); });
        if (t.size() < 2 || t[0] != 'x') throw runtime_error("thanh ghi sai: " + t);
        int n = static_cast<int>(parse_integer(t.substr(1)));
        if (n < 0 || n >= 32) throw runtime_error("thanh ghi ngoai pham vi: " + t);
        return n;
    };

    auto val = [&labels](const string& token, int pc) -> int64_t {
        string t = trim(token);
        auto it = labels.find(t);
        if (it != labels.end()) return int64_t(it->second) - pc;
        return parse_integer(t);
    };

    vector<u32> out;
    for (int pc = 0; pc < static_cast<int>(lines.size()); ++pc) {
        const string& line = lines[pc];
        size_t sep = line.find_first_of(" \t");
        string mn = (sep == string::npos) ? line : line.substr(0, sep);
        string rest = (sep == string::npos) ? "" : trim(line.substr(sep + 1));
        transform(mn.begin(), mn.end(), mn.begin(), [](unsigned char c) { return char(toupper(c)); });
        vector<string> a = split_args(rest);

        auto need = [&a, &line](size_t n) {
            if (a.size() != n) {
                throw runtime_error("sai so doi so trong lenh: " + line);
            }
        };

        if (mn == "ADD" || mn == "SUB" || mn == "AND" || mn == "OR" || mn == "XOR" || mn == "SLL" || mn == "SRL") {
            need(3);
            out.push_back(enc_r(OPS.at(mn), reg(a[0]), reg(a[1]), reg(a[2])));
        } else if (mn == "ADDI" || mn == "LW") {
            need(3);
            out.push_back(enc_i(OPS.at(mn), reg(a[0]), reg(a[1]), val(a[2], pc)));
        } else if (mn == "SW") {
            need(3); // SW rs2, rs1, imm
            out.push_back(enc_s(OPS.at("SW"), reg(a[1]), reg(a[0]), val(a[2], pc)));
        } else if (mn == "BEQ") {
            need(3); // BEQ rs1, rs2, label
            out.push_back(enc_s(OPS.at("BEQ"), reg(a[0]), reg(a[1]), val(a[2], pc)));
        } else if (mn == "JAL") {
            need(2);
            out.push_back(enc_j(OPS.at("JAL"), reg(a[0]), val(a[1], pc)));
        } else if (mn == "HALT") {
            need(0);
            out.push_back(HALT);
        } else if (mn == "NOP") {
            need(0);
            out.push_back(0);
        } else {
            throw runtime_error("lenh khong co: " + line);
        }
    }
    return out;
}

array<u32, IWORDS> make_imem(const vector<u32>& words) {
    if (words.size() > IWORDS) throw runtime_error("chuong trinh vuot qua 128 tu lenh");
    array<u32, IWORDS> mem{};
    copy(words.begin(), words.end(), mem.begin());
    return mem;
}

struct Result {
    array<u64, 32> regs{};
    array<u64, DWORDS> dmem{};
    bool fault = false;
};

// ---------------------------------------------------------------------------
// Mo hinh chuan (golden)
// ---------------------------------------------------------------------------
Result golden(const vector<u32>& words, int max_steps = 100000) {
    auto imem = make_imem(words);
    Result result;
    u32 pc = 0;

    auto write_reg = [&result](int i, u64 value) {
        if (i != 0) result.regs[i] = value;
    };

    for (int step = 0; step < max_steps; ++step) {
        u32 w = ((pc >> 2) < IWORDS) ? imem[pc >> 2] : 0xFFFFFFFFu;
        int op = int(w & 127u);
        int rd = int((w >> 7) & 31u);
        int rs1 = int((w >> 12) & 31u);
        int rs2 = int((w >> 17) & 31u);
        u64 a = result.regs[rs1], b = result.regs[rs2];
        u32 npc = pc + 4u;

        auto it = ALU_OF.find(op);
        if (it != ALU_OF.end()) {
            u64 y = 0;
            switch (it->second) {
                case 0: y = a + b; break;
                case 1: y = a - b; break;
                case 2: y = a & b; break;
                case 3: y = a | b; break;
                case 4: y = a ^ b; break;
                case 5: y = a << (b & 63u); break;
                case 6: y = a >> (b & 63u); break;
            }
            write_reg(rd, y);
        } else if (op == OPS.at("ADDI")) {
            write_reg(rd, a + sx(w >> 17, 15));
        } else if (op == OPS.at("LW") || op == OPS.at("SW")) {
            u64 imm = (op == OPS.at("LW")) ? sx(w >> 17, 15) : sx(w >> 22, 10);
            u64 addr = a + imm;
            if ((addr & 7u) != 0 || (addr >> 3) >= DWORDS) {
                result.fault = true;
                return result;
            }
            size_t index = static_cast<size_t>(addr >> 3);
            if (op == OPS.at("LW")) write_reg(rd, result.dmem[index]);
            else result.dmem[index] = b;
        } else if (op == OPS.at("BEQ")) {
            if (a == b) npc = pc + static_cast<u32>(sx(w >> 22, 10) * 4u);
        } else if (op == OPS.at("JAL")) {
            u64 imm = sx(w >> 12, 20);
            write_reg(rd, u64(pc) + 4u);
            if (imm == 0) return result;
            npc = pc + static_cast<u32>(imm * 4u);
        } else {
            result.fault = true;
            return result;
        }
        pc = npc;
    }
    throw runtime_error("golden: vuot so buoc");
}

// ---------------------------------------------------------------------------
// Giai ma lenh va ALU
// ---------------------------------------------------------------------------
struct Decoded {
    int rd = 0, rs1 = 0, rs2 = 0;
    u64 imm = 0;
    bool reg_write = false, mem_r = false, mem_w = false;
    bool src_imm = false, branch = false, jump = false;
    bool use1 = false, use2 = false, illegal = false;
    int alu = 0;
};

Decoded decode(u32 w) {
    int op = int(w & 127u);
    Decoded d;
    d.rd = int((w >> 7) & 31u);
    d.rs1 = int((w >> 12) & 31u);
    d.rs2 = int((w >> 17) & 31u);

    auto it = ALU_OF.find(op);
    if (it != ALU_OF.end()) {
        d.reg_write = true; d.alu = it->second; d.use1 = true; d.use2 = true;
    } else if (op == OPS.at("ADDI")) {
        d.reg_write = true; d.src_imm = true; d.use1 = true; d.imm = sx(w >> 17, 15);
    } else if (op == OPS.at("LW")) {
        d.reg_write = true; d.mem_r = true; d.src_imm = true; d.use1 = true; d.imm = sx(w >> 17, 15);
    } else if (op == OPS.at("SW")) {
        d.mem_w = true; d.src_imm = true; d.use1 = true; d.use2 = true; d.imm = sx(w >> 22, 10);
    } else if (op == OPS.at("BEQ")) {
        d.branch = true; d.alu = 1; d.use1 = true; d.use2 = true; d.imm = sx(w >> 22, 10);
    } else if (op == OPS.at("JAL")) {
        d.reg_write = true; d.jump = true; d.imm = sx(w >> 12, 20);
    } else {
        d.illegal = true;
    }
    return d;
}

pair<u64, bool> alu(int op, u64 a, u64 b) {
    u64 y = 0;
    switch (op) {
        case 0: y = a + b; break;
        case 1: y = a - b; break;
        case 2: y = a & b; break;
        case 3: y = a | b; break;
        case 4: y = a ^ b; break;
        case 5: y = a << (b & 63u); break;
        case 6: y = a >> (b & 63u); break;
        default: y = 0; break;
    }
    return {y, y == 0};
}

struct IDReg {
    bool v = false;
    u32 pc = 0, instr = 0;
};

struct EXReg {
    bool v = false, illegal = false, reg_write = false, mem_r = false, mem_w = false;
    bool src_imm = false, branch = false, jump = false, use1 = false, use2 = false;
    int alu = 0, rd = 0, rs1 = 0, rs2 = 0;
    u64 v1 = 0, v2 = 0, imm = 0;
    u32 pc = 0;
};

struct WBReg {
    bool v = false, reg_write = false, mem_r = false, mem_w = false;
    int rd = 0;
    u64 y = 0, load = 0, store = 0, addr = 0;
};

class Pipeline {
public:
    array<u32, IWORDS> imem{};
    array<u64, DWORDS> dmem{};
    array<u64, 32> regs{};
    u32 pc = 0;
    bool halted = false, fault = false;
    IDReg id;
    EXReg ex;
    WBReg wb;
    int cycles = 0;

    explicit Pipeline(const vector<u32>& words) : imem(make_imem(words)) {}

    void step() {
        const EXReg old_ex = ex;
        const WBReg old_wb = wb;
        const IDReg old_id = id;

        // WB (to hop)
        bool wb_we = old_wb.v && old_wb.reg_write && old_wb.rd != 0;
        u64 wb_data = old_wb.mem_r ? old_wb.load : old_wb.y;

        // Decode (to hop)
        Decoded d = decode(old_id.instr);
        auto rf_read = [&](int sel) -> u64 {
            if (sel == 0) return 0;
            if (wb_we && old_wb.rd == sel) return wb_data;
            return regs[sel];
        };

        // Execute (to hop)
        u64 fwd_a = (wb_we && old_ex.use1 && old_ex.rs1 == old_wb.rd) ? wb_data : old_ex.v1;
        u64 fwd_b = (wb_we && old_ex.use2 && old_ex.rs2 == old_wb.rd) ? wb_data : old_ex.v2;
        u64 alu_b = old_ex.src_imm ? old_ex.imm : fwd_b;
        auto alu_result = alu(old_ex.alu, fwd_a, alu_b);
        u64 alu_y = alu_result.first;
        bool alu_z = alu_result.second;
        u64 ex_addr = fwd_a + old_ex.imm;
        bool is_mem = old_ex.mem_r || old_ex.mem_w;
        bool mem_ok = (ex_addr & 7u) == 0 && (ex_addr >> 3) < DWORDS;
        size_t didx = static_cast<size_t>((ex_addr >> 3) & (DWORDS - 1));
        u64 ex_result = old_ex.jump ? u64(old_ex.pc + 4u) : alu_y;
        u32 target = old_ex.pc + (static_cast<u32>(old_ex.imm) << 2);
        u64 load_data;
        if (old_wb.v && old_wb.mem_w && old_wb.addr == ex_addr) load_data = old_wb.store;
        else load_data = dmem[didx];

        bool trap = old_ex.v && (old_ex.illegal || (is_mem && !mem_ok));
        bool halt_now = old_ex.v && !trap && old_ex.jump && old_ex.imm == 0;
        bool stop = trap || halt_now;
        bool taken = old_ex.v && !trap && (old_ex.jump || (old_ex.branch && alu_z));
        bool fetch_ok = (pc & 3u) == 0 && (pc >> 2) < IWORDS;

        // Tinh trang thai ke tiep
        u32 next_pc = pc;
        IDReg next_id = old_id;
        if (halted || stop) {
            next_id.v = false;
        } else if (taken) {
            next_pc = target;
            next_id.v = false;
        } else {
            next_pc = pc + 4u;
            next_id.v = true;
            next_id.pc = pc;
            next_id.instr = fetch_ok ? imem[(pc >> 2) & (IWORDS - 1)] : 0xFFFFFFFFu;
        }

        EXReg next_ex;
        if (old_id.v && !taken && !stop) {
            next_ex.v = true;
            next_ex.pc = old_id.pc;
            next_ex.rd = d.rd; next_ex.rs1 = d.rs1; next_ex.rs2 = d.rs2;
            next_ex.illegal = d.illegal;
            next_ex.reg_write = d.reg_write; next_ex.mem_r = d.mem_r; next_ex.mem_w = d.mem_w;
            next_ex.src_imm = d.src_imm; next_ex.branch = d.branch; next_ex.jump = d.jump;
            next_ex.use1 = d.use1; next_ex.use2 = d.use2; next_ex.alu = d.alu;
            next_ex.v1 = rf_read(d.rs1); next_ex.v2 = rf_read(d.rs2); next_ex.imm = d.imm;
        } else {
            next_ex = old_ex;
            next_ex.v = false;
            next_ex.illegal = false; next_ex.branch = false; next_ex.jump = false;
            next_ex.reg_write = false; next_ex.mem_r = false; next_ex.mem_w = false;
            next_ex.use1 = false; next_ex.use2 = false;
        }

        WBReg next_wb;
        if (old_ex.v && !trap) {
            next_wb.v = true;
            next_wb.rd = old_ex.rd;
            next_wb.reg_write = old_ex.reg_write;
            next_wb.mem_r = old_ex.mem_r;
            next_wb.mem_w = old_ex.mem_w;
            next_wb.y = ex_result;
            next_wb.load = load_data;
            next_wb.store = fwd_b;
            next_wb.addr = ex_addr;
        } else {
            next_wb = old_wb;
            next_wb.v = false;
            next_wb.reg_write = false;
            next_wb.mem_r = false;
            next_wb.mem_w = false;
        }

        // Canh len: ghi regfile / dmem roi cap nhat cac thanh ghi
        if (wb_we) regs[old_wb.rd] = wb_data;
        if (old_wb.v && old_wb.mem_w) {
            dmem[(old_wb.addr >> 3) & (DWORDS - 1)] = old_wb.store;
        }
        pc = next_pc;
        halted = halted || stop;
        fault = fault || trap;
        id = next_id;
        ex = next_ex;
        wb = next_wb;
        ++cycles;
    }
};

struct PipelineResult {
    array<u64, 32> regs{};
    array<u64, DWORDS> dmem{};
    bool fault = false;
    int cycles = 0;
};

PipelineResult run_pipeline(const vector<u32>& words, int max_cycles = 5000) {
    Pipeline p(words);
    while (!p.halted) {
        p.step();
        if (p.cycles > max_cycles) throw runtime_error("pipeline timeout");
    }
    for (int i = 0; i < 4; ++i) p.step(); // cho lenh cuoi commit
    return {p.regs, p.dmem, p.fault, p.cycles};
}

// ---------------------------------------------------------------------------
// Kiem thu co dinh
// ---------------------------------------------------------------------------
struct DirectedTest {
    string name, source;
    unordered_map<int, u64> expected_regs;
    unordered_map<int, u64> expected_mem;
    bool expected_fault;
};

vector<DirectedTest> make_directed_tests() {
    return {
        {"smoke (giong testbench SV)", R"ASM(
            addi x1, x0, 5
            addi x2, x1, 7         ; chuyen tiep kc 1
            addi x3, x0, 1
            add  x4, x1, x2        ; bypass regfile kc 2
            sw   x4, x0, 8
            lw   x5, x0, 8         ; ne SW->LW
            beq  x5, x4, over
            addi x6, x0, 99        ; bi bo qua
over:       addi x7, x0, 3
            halt
        )ASM", {{1, 5}, {2, 12}, {3, 1}, {4, 17}, {5, 17}, {6, 0}, {7, 3}}, {{1, 17}}, false},

        {"vong lap tinh 5+4+3+2+1", R"ASM(
            addi x1, x0, 5
            addi x2, x0, 0
            addi x3, x0, 1
loop:       add  x2, x2, x1
            sub  x1, x1, x3
            beq  x1, x0, done
            jal  x0, loop
done:       halt
        )ASM", {{1, 0}, {2, 15}}, {}, false},

        {"JAL ghi dia chi tra ve", R"ASM(
            jal  x5, tgt           ; x5 = 4
            addi x6, x0, 99        ; bi bo qua
tgt:        addi x7, x0, 7
            halt
        )ASM", {{5, 4}, {6, 0}, {7, 7}}, {}, false},

        {"dich bit & logic 64-bit", R"ASM(
            addi x1, x0, 1
            addi x2, x0, 63
            sll  x3, x1, x2        ; 1<<63
            srl  x4, x3, x2        ; ve 1
            addi x5, x0, -1
            and  x6, x5, x3
            xor  x7, x5, x5
            or   x8, x7, x1
            halt
        )ASM", {{3, u64(1) << 63}, {4, 1}, {5, M64}, {6, u64(1) << 63}, {7, 0}, {8, 1}}, {}, false},

        {"ghi vao x0 bi bo qua", R"ASM(
            addi x0, x0, 5
            add  x1, x0, x0
            halt
        )ASM", {{1, 0}}, {}, false},

        {"LW lech hang -> fault, khong commit", R"ASM(
            addi x1, x0, 7
            lw   x2, x0, 3
            addi x3, x0, 9         ; khong duoc thuc thi
            halt
        )ASM", {{1, 7}, {2, 0}, {3, 0}}, {}, true},

        {"SW ngoai DMEM -> fault", R"ASM(
            addi x1, x0, 5
            sw   x1, x0, 511
            halt
        )ASM", {{1, 5}}, {}, true},

        {"opcode sai -> fault", "", {}, {}, true},
        {"chay ra ngoai IMEM -> fault", "addi x1, x0, 1", {{1, 1}}, {}, true}
    };
}

vector<u32> test_words(const DirectedTest& t) {
    return t.source.empty() ? vector<u32>{0x0000007Fu} : assemble(t.source);
}

void run_directed(const vector<DirectedTest>& tests) {
    for (const auto& t : tests) {
        vector<u32> words = test_words(t);
        Result g = golden(words);
        PipelineResult p = run_pipeline(words);
        for (const auto& item : t.expected_regs) {
            int r = item.first;
            u64 value = item.second;
            if (g.regs[r] != value) {
                ostringstream m; m << "[" << t.name << "] golden x" << r << " sai"; throw runtime_error(m.str());
            }
            if (p.regs[r] != value) {
                ostringstream m; m << "[" << t.name << "] pipeline x" << r << " sai"; throw runtime_error(m.str());
            }
        }
        for (const auto& item : t.expected_mem) {
            int m = item.first;
            u64 value = item.second;
            if (g.dmem[m] != value || p.dmem[m] != value)
                throw runtime_error("[" + t.name + "] dmem sai");
        }
        if (g.fault != t.expected_fault || p.fault != t.expected_fault)
            throw runtime_error("[" + t.name + "] fault sai");
        if (g.regs != p.regs || g.dmem != p.dmem)
            throw runtime_error("[" + t.name + "] golden != pipeline");
        cout << "  OK  " << t.name << "  (" << p.cycles << " chu ky)\n";
    }
}

// ---------------------------------------------------------------------------
// Sinh chuong trinh ngau nhien va doi chieu
// ---------------------------------------------------------------------------
int randint(mt19937_64& rng, int lo, int hi) {
    uniform_int_distribution<int> dist(lo, hi);
    return dist(rng);
}

double rand01(mt19937_64& rng) {
    return generate_canonical<double, 53>(rng);
}

u32 random_program(mt19937_64& rng, int n, vector<u32>& output) {
    auto R = [&]() { return randint(rng, 0, 7); };
    output.clear();
    for (int i = 0; i < n; ++i) {
        double k = rand01(rng);
        if (k < 0.38) {
            const int ops[] = {0, 1, 8, 9, 10, 16, 17};
            output.push_back(enc_r(ops[randint(rng, 0, 6)], R(), R(), R()));
        } else if (k < 0.55) {
            bool big = rand01(rng) < 0.15;
            int imm = big ? randint(rng, -16384, 16383) : randint(rng, -40, 40);
            output.push_back(enc_i(OPS.at("ADDI"), R(), R(), imm));
        } else if (k < 0.67) {
            int imm = (rand01(rng) < 0.93) ? 8 * randint(rng, 0, 31) : randint(rng, -20, 300);
            int rs1 = (rand01(rng) < 0.9) ? 0 : R();
            output.push_back(enc_i(OPS.at("LW"), R(), rs1, imm));
        } else if (k < 0.79) {
            int imm = (rand01(rng) < 0.93) ? 8 * randint(rng, 0, 31) : randint(rng, -20, 300);
            int rs1 = (rand01(rng) < 0.9) ? 0 : R();
            output.push_back(enc_s(OPS.at("SW"), rs1, R(), imm));
        } else if (k < 0.93) {
            output.push_back(enc_s(OPS.at("BEQ"), R(), R(), randint(rng, 1, 4)));
        } else if (k < 0.985) {
            output.push_back(enc_j(OPS.at("JAL"), R(), randint(rng, 1, 3)));
        } else {
            const u32 bad[] = {0x7F, 0x07, 0x02, 0xFFFFFFFFu};
            output.push_back(bad[randint(rng, 0, 3)]);
        }
    }
    output.push_back(HALT);
    return 0;
}

void run_random(int n_programs, uint64_t seed = 2026) {
    mt19937_64 rng(seed);
    int faults = 0;
    vector<u32> words;
    for (int it = 0; it < n_programs; ++it) {
        random_program(rng, randint(rng, 5, 50), words);
        Result g = golden(words);
        PipelineResult p = run_pipeline(words);
        if (g.regs != p.regs || g.dmem != p.dmem || g.fault != p.fault) {
            cout << "LECH o chuong trinh #" << it << ":";
            for (u32 x : words) cout << " " << hex << showbase << x;
            cout << dec << noshowbase << "\n";
            for (int i = 0; i < 32; ++i) {
                if (g.regs[i] != p.regs[i]) {
                    cout << "   x" << i << ": golden=" << hex << showbase << g.regs[i]
                         << " pipeline=" << p.regs[i] << dec << noshowbase << "\n";
                }
            }
            cout << "   fault golden/pipeline: " << g.fault << " " << p.fault << "\n";
            throw runtime_error("kiem thu ngau nhien phat hien sai lech");
        }
        faults += g.fault;
    }
    cout << "  OK  " << n_programs << " chuong trinh ngau nhien khop 100% ("
         << faults << " trong so do ket thuc bang fault)\n";
}

// ---------------------------------------------------------------------------
// Chuong trinh chinh
// ---------------------------------------------------------------------------
int main() {
    try {
        vector<DirectedTest> tests = make_directed_tests();

        cout << "HELIX-1 - KIEM THU C++14 (GCC 6.3.0)\n";
        cout << "Kiem thu truc tiep:\n";
        run_directed(tests);

        cout << "Kiem thu ngau nhien (pipeline vs golden):\n";
        run_random(5000);

        cout << "\nHOAN TAT: cac kiem thu mo hinh deu PASS.\n";
        cout << "Luu y: de mo phong file SystemVerilog (.sv), can cai Icarus Verilog rieng.\n";
    } catch (const exception& e) {
        cerr << "LOI: " << e.what() << "\n";
        return 1;
    }
    return 0;
}
