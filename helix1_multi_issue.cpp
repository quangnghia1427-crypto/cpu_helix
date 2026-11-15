// HELIX-1 - bo cong cu kiem chung (ban C++17)
// CPU mo phong In-Order 6-wide: toi da 6 lenh ALU doc lap/cycle (6 ALU 64-bit).
// Khong phai Out-of-Order; RAW/WAW se tach goi issue. Memory/branch/jump chay rieng.
// IMEM dong; DMEM mac dinh 64 tu 64-bit, co the doi bang tham so --dmem.
    // Bien dich: g++ -std=c++17 -O2 -Wall -Wextra -o helix1_tools helix1_tools.cpp
    // Chay:      ./helix1_tools
    // Neu may co iverilog va vvp, chuong trinh se tu dong doi chieu them RTL that.
    #include <algorithm>
    #include <array>
    #include <chrono>
    #include <cstdint>
    #include <cstdlib>
    #include <filesystem>
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
    namespace fs = std::filesystem;
    using u32 = uint32_t;
    using u64 = uint64_t;
    constexpr u64 M64 = numeric_limits<u64>::max();
    constexpr u32 M32 = numeric_limits<u32>::max();
    // Bo nho du lieu mac dinh: 64 tu, moi tu 64-bit (512 byte).
    // IMEM va DMEM dung vector nen co the mo rong theo kich thuoc chuong trinh/cau hinh.
    constexpr size_t DEFAULT_DWORDS = 64;
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
    // IMEM co kich thuoc theo chuong trinh, khong con gioi han 128 lenh.
    vector<u32> make_imem(const vector<u32>& words) {
        return words;
    }
    struct Result {
        array<u64, 32> regs{};
        vector<u64> dmem;
        bool fault = false;
    };
    // ---------------------------------------------------------------------------
    // Mo hinh chuan (golden)
    // ---------------------------------------------------------------------------
    Result golden(const vector<u32>& words, int max_steps = 100000,
                  size_t data_words = DEFAULT_DWORDS) {
        if (data_words == 0) throw runtime_error("DMEM phai co it nhat 1 tu 64-bit");
        auto imem = make_imem(words);
        Result result;
        result.dmem.assign(data_words, 0);
        u32 pc = 0;
        auto write_reg = [&result](int i, u64 value) {
            if (i != 0) result.regs[i] = value;
        };
        for (int step = 0; step < max_steps; ++step) {
            u32 w = ((pc & 3u) == 0 && (pc >> 2) < imem.size())
                        ? imem[pc >> 2] : 0xFFFFFFFFu;
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
                if ((addr & 7u) != 0 || (addr >> 3) >= result.dmem.size()) {
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
    // ---------------------------------------------------------------------------
    // Multi-issue In-Order: toi da 6 lenh ALU doc lap moi chu ky.
    // Moi lane la mot ALU 64-bit rieng. RAW/WAW trong cung goi issue se
    // lam goi dung lai truoc lenh phu thuoc; lenh do duoc chay o chu ky sau.
    // LW/SW/BEQ/JAL duoc xu ly rieng de giu dung thu tu chuong trinh.
    // ---------------------------------------------------------------------------
    constexpr int ISSUE_WIDTH = 6;

    struct PipelineResult {
        array<u64, 32> regs{};
        vector<u64> dmem;
        bool fault = false;
        int cycles = 0;
        int issued = 0;
        int alu_ops = 0;
        int peak_issue = 0;
    };

    class Pipeline {
    public:
        vector<u32> imem;
        vector<u64> dmem;
        array<u64, 32> regs{};
        u32 pc = 0;
        bool halted = false, fault = false;
        int cycles = 0;
        int issued = 0;
        int alu_ops = 0;
        int peak_issue = 0;

        explicit Pipeline(const vector<u32>& words, size_t data_words = DEFAULT_DWORDS)
            : imem(make_imem(words)), dmem(data_words, 0) {
            if (data_words == 0)
                throw runtime_error("DMEM phai co it nhat 1 tu 64-bit");
        }

        bool fetch(u32 at, u32& word) const {
            if ((at & 3u) != 0 || (at >> 2) >= imem.size()) return false;
            word = imem[at >> 2];
            return true;
        }

        bool is_alu_instruction(const Decoded& d, u32 word) const {
            int op = int(word & 127u);
            return !d.illegal && (ALU_OF.count(op) != 0 || op == OPS.at("ADDI"));
        }

        void execute_one_non_alu(u32 word) {
            Decoded d = decode(word);
            ++issued;

            if (d.illegal) {
                fault = true;
                halted = true;
                return;
            }

            if (d.mem_r || d.mem_w) {
                u64 base = regs[d.rs1];
                u64 addr = base + d.imm;
                bool mem_ok = ((addr & 7u) == 0) && ((addr >> 3) < dmem.size());
                if (!mem_ok) {
                    fault = true;
                    halted = true;
                    return;
                }
                size_t index = static_cast<size_t>(addr >> 3);
                if (d.mem_r) {
                    if (d.rd != 0) regs[d.rd] = dmem[index];
                } else {
                    dmem[index] = regs[d.rs2];
                }
                pc += 4u;
                return;
            }

            if (d.branch) {
                if (regs[d.rs1] == regs[d.rs2])
                    pc += static_cast<u32>(d.imm * 4u);
                else
                    pc += 4u;
                return;
            }

            if (d.jump) {
                if (d.rd != 0) regs[d.rd] = u64(pc) + 4u;
                if (d.imm == 0) {
                    halted = true; // HALT = JAL x0, 0
                } else {
                    pc += static_cast<u32>(d.imm * 4u);
                }
                return;
            }

            // Lenh khong phai ALU, memory, branch hay jump la opcode khong hop le.
            fault = true;
            halted = true;
        }

        void step() {
            if (halted) return;

            u32 first_word = 0;
            if (!fetch(pc, first_word)) {
                ++cycles;
                fault = true;
                halted = true;
                return;
            }

            Decoded first = decode(first_word);
            if (!is_alu_instruction(first, first_word)) {
                execute_one_non_alu(first_word);
                ++cycles;
                peak_issue = max(peak_issue, 1);
                return;
            }

            // Tao mot goi issue toi da 6 lenh ALU lien tiep va doc lap.
            vector<Decoded> bundle;
            bundle.reserve(ISSUE_WIDTH);
            array<bool, 32> written_in_bundle{};
            u32 scan_pc = pc;

            while (static_cast<int>(bundle.size()) < ISSUE_WIDTH) {
                u32 word = 0;
                if (!fetch(scan_pc, word)) break;

                Decoded d = decode(word);
                if (!is_alu_instruction(d, word)) break;

                // RAW: lenh sau doc ket qua cua lenh truoc trong cung bundle.
                bool raw_hazard = (d.use1 && written_in_bundle[d.rs1]) ||
                                  (d.use2 && written_in_bundle[d.rs2]);
                // WAW: hai lane cung ghi mot thanh ghi, can tach bundle.
                bool waw_hazard = d.reg_write && d.rd != 0 && written_in_bundle[d.rd];
                if (raw_hazard || waw_hazard) break;

                bundle.push_back(d);
                if (d.reg_write && d.rd != 0) written_in_bundle[d.rd] = true;
                scan_pc += 4u;
            }

            // Tinh song song ket qua 6 ALU tren snapshot thanh ghi dau chu ky.
            // Ghi thanh ghi chi xay ra sau khi tat ca lane da tinh xong.
            array<u64, ISSUE_WIDTH> lane_result{};
            array<int, ISSUE_WIDTH> lane_rd{};
            array<bool, ISSUE_WIDTH> lane_write{};

            for (size_t lane = 0; lane < bundle.size(); ++lane) {
                const Decoded& d = bundle[lane];
                u64 a = d.use1 ? regs[d.rs1] : 0;
                u64 b = d.src_imm ? d.imm : (d.use2 ? regs[d.rs2] : 0);
                lane_result[lane] = alu(d.alu, a, b).first;
                lane_rd[lane] = d.rd;
                lane_write[lane] = d.reg_write && d.rd != 0;
            }

            for (size_t lane = 0; lane < bundle.size(); ++lane) {
                if (lane_write[lane]) regs[lane_rd[lane]] = lane_result[lane];
            }

            int count = static_cast<int>(bundle.size());
            pc = scan_pc;
            issued += count;
            alu_ops += count;
            peak_issue = max(peak_issue, count);
            ++cycles;
        }

        PipelineResult result() const {
            return {regs, dmem, fault, cycles, issued, alu_ops, peak_issue};
        }
    };

    PipelineResult run_pipeline(const vector<u32>& words, int max_cycles = 5000,
                                size_t data_words = DEFAULT_DWORDS) {
        Pipeline p(words, data_words);
        while (!p.halted) {
            p.step();
            if (p.cycles > max_cycles) throw runtime_error("multi-issue timeout");
        }
        return p.result();
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
    vector<DirectedTest> make_directed_tests(size_t data_words = DEFAULT_DWORDS) {
        vector<DirectedTest> tests = {
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
                addi x2, x0, 512
                sw   x1, x2, 0
                halt
            )ASM", {{1, 5}, {2, 512}}, {}, true},
            {"DMEM 64 tu: ghi/doc tu thu 64", R"ASM(
                addi x1, x0, 42
                sw   x1, x0, 504
                lw   x2, x0, 504
                halt
            )ASM", {{1, 42}, {2, 42}}, {{63, 42}}, false},
            {"MULTI-ISSUE 6 ALU: 6 lenh doc lap moi chu ky", R"ASM(
                addi x1, x0, 10
                addi x2, x0, 20
                addi x3, x0, 30
                addi x4, x0, 40
                addi x5, x0, 50
                addi x6, x0, 60
                add  x7, x1, x2
                sub  x8, x4, x3
                xor  x9, x5, x6
                and  x10, x1, x2
                or   x11, x3, x4
                sll  x12, x1, x3
                halt
            )ASM", {{7, 30}, {8, 10}, {9, 14}, {10, 0}, {11, 62}, {12, u64(10) << 30}}, {}, false},
            {"opcode sai -> fault", "", {}, {}, true},
            {"chay ra ngoai IMEM -> fault", "addi x1, x0, 1", {{1, 1}}, {}, true}
        };
        string long_program;
        for (int i = 0; i < 300; ++i) long_program += "nop\n";
        long_program += "addi x1, x0, 77\nhalt\n";
        tests.push_back({"IMEM dong: chuong trinh hon 128 lenh", long_program, {{1, 77}}, {}, false});

        // Tao dia chi byte nam ngay sau DMEM bang cach dung ADD/SLL-style doubling.
        // Cach nay khong bi gioi han boi do rong immediate ADDI 15-bit.
        uint64_t out_of_range_addr = static_cast<uint64_t>(data_words) * 8u;
        ostringstream out_of_range_program;
        out_of_range_program << "addi x1, x0, 5\naddi x2, x0, 0\n";
        int highest_bit = 63;
        while (highest_bit > 0 && ((out_of_range_addr >> highest_bit) & 1u) == 0)
            --highest_bit;
        for (int bit = highest_bit; bit >= 0; --bit) {
            out_of_range_program << "add x2, x2, x2\n";
            if ((out_of_range_addr >> bit) & 1u)
                out_of_range_program << "addi x2, x2, 1\n";
        }
        out_of_range_program << "sw x1, x2, 0\nhalt\n";
        for (auto& test : tests) {
            if (test.name == "SW ngoai DMEM -> fault") {
                test.source = out_of_range_program.str();
                test.expected_regs[2] = out_of_range_addr;
                break;
            }
        }
        return tests;
    }
    vector<u32> test_words(const DirectedTest& t) {
        return t.source.empty() ? vector<u32>{0x0000007Fu} : assemble(t.source);
    }
    void run_directed(const vector<DirectedTest>& tests, size_t data_words = DEFAULT_DWORDS) {
        for (const auto& t : tests) {
            vector<u32> words = test_words(t);
            Result g = golden(words, 100000, data_words);
            PipelineResult p = run_pipeline(words, 5000, data_words);
            for (auto [r, value] : t.expected_regs) {
                if (g.regs[r] != value) {
                    ostringstream m; m << "[" << t.name << "] golden x" << r << " sai"; throw runtime_error(m.str());
                }
                if (p.regs[r] != value) {
                    ostringstream m; m << "[" << t.name << "] pipeline x" << r << " sai"; throw runtime_error(m.str());
                }
            }
            for (auto [m, value] : t.expected_mem) {
                if (g.dmem[m] != value || p.dmem[m] != value)
                    throw runtime_error("[" + t.name + "] dmem sai");
            }
            if (g.fault != t.expected_fault || p.fault != t.expected_fault)
                throw runtime_error("[" + t.name + "] fault sai");
            if (g.regs != p.regs || g.dmem != p.dmem)
                throw runtime_error("[" + t.name + "] golden != multi-issue");
            if (t.name.find("MULTI-ISSUE 6 ALU") != string::npos && p.peak_issue != ISSUE_WIDTH)
                throw runtime_error("[" + t.name + "] khong phat hanh du 6 ALU trong mot chu ky");
            cout << "  OK  " << t.name << "  (" << p.cycles << " chu ky, "
                 << p.issued << " lenh, dinh " << p.peak_issue << " lenh/chu ky)\n";
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
    u32 random_program(mt19937_64& rng, int n, vector<u32>& output,
                       size_t data_words = DEFAULT_DWORDS) {
        if (data_words == 0) throw runtime_error("DMEM phai co it nhat 1 tu 64-bit");
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
                int max_word = static_cast<int>(min<size_t>(63, data_words - 1));
                int imm = (rand01(rng) < 0.93) ? 8 * randint(rng, 0, max_word) : randint(rng, -20, 300);
                int rs1 = (rand01(rng) < 0.9) ? 0 : R();
                output.push_back(enc_i(OPS.at("LW"), R(), rs1, imm));
            } else if (k < 0.79) {
                int max_word = static_cast<int>(min<size_t>(63, data_words - 1));
                int imm = (rand01(rng) < 0.93) ? 8 * randint(rng, 0, max_word) : randint(rng, -20, 300);
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
    void run_random(int n_programs, uint64_t seed = 2026,
                    size_t data_words = DEFAULT_DWORDS) {
        mt19937_64 rng(seed);
        int faults = 0;
        long long total_issued = 0;
        long long total_cycles = 0;
        int observed_peak = 0;
        vector<u32> words;
        for (int it = 0; it < n_programs; ++it) {
            random_program(rng, randint(rng, 5, 50), words, data_words);
            Result g = golden(words, 100000, data_words);
            PipelineResult p = run_pipeline(words, 5000, data_words);
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
            total_issued += p.issued;
            total_cycles += p.cycles;
            observed_peak = max(observed_peak, p.peak_issue);
        }
        double ipc = total_cycles ? double(total_issued) / double(total_cycles) : 0.0;
        cout << "  OK  " << n_programs << " chuong trinh ngau nhien khop 100% ("
             << faults << " chuong trinh fault)\n";
        cout << "  Throughput trung binh: " << fixed << setprecision(3) << ipc
             << " lenh/chu ky; issue rong nhat quan sat: " << observed_peak << " lenh/chu ky\n";
    }
    // ---------------------------------------------------------------------------
    // Doi chieu RTL that neu may co iverilog va vvp
    // ---------------------------------------------------------------------------
    string shell_quote(const string& s) {
        string out = "'";
        for (char c : s) {
            if (c == '\'') out += "'\\''";
            else out += c;
        }
        out += "'";
        return out;
    }
    string read_file(const fs::path& path) {
        ifstream f(path);
        if (!f) throw runtime_error("khong mo duoc file: " + path.string());
        ostringstream ss; ss << f.rdbuf(); return ss.str();
    }
    void run_rtl_tests(const vector<vector<u32>>& progs, const fs::path& source_dir,
                       size_t data_words = DEFAULT_DWORDS) {
        if (system("command -v iverilog >/dev/null 2>&1") != 0 ||
            system("command -v vvp >/dev/null 2>&1") != 0) {
            cout << "  (khong co iverilog -> bo qua doi chieu RTL that; xem README)\n";
            return;
        }
        auto stamp = chrono::steady_clock::now().time_since_epoch().count();
        fs::path tmp = fs::temp_directory_path() / ("helix1_" + to_string(stamp));
        fs::create_directories(tmp);
        fs::path sim = tmp / "sim";
        vector<fs::path> srcs = {
            source_dir / "rtl" / "alu.sv",
            source_dir / "rtl" / "decoder.sv",
            source_dir / "rtl" / "regfile.sv",
            source_dir / "rtl" / "helix1_cpu.sv",
            source_dir / "tb" / "cpu_tb.sv"
        };
        string compile_cmd = "iverilog -g2012 -o " + shell_quote(sim.string());
        for (const auto& p : srcs) compile_cmd += " " + shell_quote(p.string());
        if (system(compile_cmd.c_str()) != 0) throw runtime_error("iverilog bien dich RTL that that bai");
        fs::path smoke_file = tmp / "smoke.txt";
        string smoke_cmd = "vvp " + shell_quote(sim.string()) + " > " + shell_quote(smoke_file.string()) + " 2>&1";
        if (system(smoke_cmd.c_str()) != 0) throw runtime_error("chay RTL smoke test that bai");
        string smoke = read_file(smoke_file);
        string last_line;
        {
            stringstream ss(smoke); string line;
            while (getline(ss, line)) if (!trim(line).empty()) last_line = line;
        }
        cout << "  RTL smoke: " << last_line << "\n";
        if (smoke.find("PASS") == string::npos) throw runtime_error("RTL smoke test khong PASS: " + smoke);
        int bad = 0;
        for (size_t i = 0; i < progs.size(); ++i) {
            fs::path hex_file = tmp / ("p" + to_string(i) + ".hex");
            fs::path out_file = tmp / ("o" + to_string(i) + ".txt");
            {
                ofstream f(hex_file);
                if (!f) throw runtime_error("khong tao duoc file hex");
                for (u32 w : progs[i]) f << hex << nouppercase << setw(8) << setfill('0') << w << "\n";
            }
            string cmd = "vvp " + shell_quote(sim.string()) + " +PROG=" + shell_quote(hex_file.string()) +
                         " +OUT=" + shell_quote(out_file.string()) + " > /dev/null 2>&1";
            if (system(cmd.c_str()) != 0) throw runtime_error("vvp loi o chuong trinh RTL #" + to_string(i));
            unordered_map<string, u64> got;
            {
                ifstream f(out_file);
                string key, value;
                while (f >> key >> value) {
                    if (key == "FAULT") got[key] = stoull(value, nullptr, 10);
                    else got[key] = stoull(value, nullptr, 16);
                }
            }
            Result g = golden(progs[i], 100000, data_words);
            bool ok = got.count("FAULT") && bool(got["FAULT"]) == g.fault;
            for (int r = 1; r < 32; ++r) {
                string key = "X" + to_string(r);
                if (!got.count(key) || got[key] != g.regs[r]) ok = false;
            }
            for (size_t m = 0; m < g.dmem.size(); ++m) {
                string key = "M" + to_string(m);
                if (!got.count(key) || got[key] != g.dmem[m]) ok = false;
            }
            if (!ok) {
                ++bad;
                cout << "  RTL LECH o chuong trinh #" << i << ":";
                for (u32 w : progs[i]) cout << " " << hex << showbase << w;
                cout << dec << noshowbase << "\n";
            }
        }
        if (bad == 0) cout << "  RTL that khop mo hinh chuan tren " << progs.size() << " chuong trinh\n";
        else cout << "  RTL that co " << bad << " chuong trinh lech\n";
        if (bad) throw runtime_error("doi chieu RTL that that bai");
    }
    int main(int argc, char** argv) {
        try {
            size_t data_words = DEFAULT_DWORDS;
            if (argc == 3 && string(argv[1]) == "--dmem") {
                data_words = stoull(argv[2]);
            } else if (argc != 1) {
                throw runtime_error("Cach dung: ./helix1_tools [--dmem so_tu_64_bit]");
            }
            if (data_words < 64 ||
                data_words > numeric_limits<u64>::max() / 8u)
                throw runtime_error("DMEM phai co it nhat 64 tu va kich thuoc byte khong duoc tran 64-bit");

            fs::path source_dir = fs::absolute(argv[0]).parent_path();
            vector<DirectedTest> tests = make_directed_tests(data_words);
            cout << "HELIX-1 C++17 | In-Order 6-wide | 6 ALU 64-bit | IMEM dong\n";
            cout << "DMEM: " << data_words << " tu x 64-bit (" << data_words * 8 << " byte)\n";
            cout << "Kiem thu truc tiep:\n";
            run_directed(tests, data_words);
            cout << "Kiem thu ngau nhien (mo hinh chu ky vs mo hinh chuan):\n";
            run_random(5000, 2026, data_words);
            cout << "Doi chieu RTL: bo qua RTL cu (single-issue).\n";
            cout << "Can cap nhat RTL thanh 6-wide va tao 6 ALU lanes truoc khi doi chieu FPGA/iverilog.\n";
        } catch (const exception& e) {
            cerr << "LOI: " << e.what() << "\n";
            return 1;
        }
        return 0;
    }