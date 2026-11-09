#!/usr/bin/env python3
"""Instruction counts of the firmware of bench/emu/fw under the Unicorn emulator (ARM Cortex-M4 or RISC-V 32).
Usage: run.py ARCH ELF SEL...      ARCH: arm | riscv.   SEL: 440 441 442 443 444 650 ... (see fw/src/main.rs); 444/654/874 first
run the preparation (443/653/873) in the same session and count only the verify.
Prints `SEL instructions loads stores result`. Instruction counts are not cycle counts."""
import struct, sys
from unicorn import *
from unicorn.arm_const import *
from unicorn.riscv_const import *

BASE, SIZE, STOP = 0x20000000, 0x200000, 0x201FF800


def load_elf(path):
    d = open(path, 'rb').read()
    assert d[:4] == b'\x7fELF' and d[4] == 1 and d[5] == 1
    e_phoff, e_shoff = struct.unpack_from('<II', d, 28)
    e_phentsize, e_phnum, e_shentsize, e_shnum, e_shstrndx = struct.unpack_from('<HHHHH', d, 42)
    segs = []
    for i in range(e_phnum):
        p_type, p_off, p_va, p_pa, p_fsz, p_msz, p_flags, p_al = struct.unpack_from('<IIIIIIII', d, e_phoff + i * e_phentsize)
        if p_type == 1 and p_msz:
            segs.append((p_va, d[p_off:p_off + p_fsz]))
    syms = {}
    for i in range(e_shnum):
        sh = struct.unpack_from('<IIIIIIIIII', d, e_shoff + i * e_shentsize)
        if sh[1] == 2:  # SHT_SYMTAB
            strsh = struct.unpack_from('<IIIIIIIIII', d, e_shoff + sh[6] * e_shentsize)
            for j in range(sh[5] // 16):
                st_name, st_value, st_size, st_info, st_other, st_shndx = struct.unpack_from('<IIIBBH', d, sh[4] + j * 16)
                n = d[strsh[4] + st_name:d.index(b'\0', strsh[4] + st_name)].decode()
                syms[n] = st_value
    return segs, syms


def session(arch, elf, seq):
    segs, syms = load_elf(elf)
    if arch == 'arm':
        uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB | UC_MODE_MCLASS)
        uc.ctl_set_cpu_model(UC_CPU_ARM_CORTEX_M4)
    else:
        uc = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    uc.mem_map(BASE, SIZE)
    for va, data in segs:
        uc.mem_write(va, data)
    out = []
    for sel, count in seq:
        uc.mem_write(syms['SEL'], struct.pack('<I', sel))
        uc.mem_write(syms['RESULT'], struct.pack('<I', 0xFFFFFFFF))
        n = [0, 0, 0]
        if count:
            def hc(u, a, s, ud): n[0] += 1
            def hr(u, t, a, s, v, ud): n[1] += 1
            def hw(u, t, a, s, v, ud): n[2] += 1
            h = [uc.hook_add(UC_HOOK_CODE, hc), uc.hook_add(UC_HOOK_MEM_READ, hr), uc.hook_add(UC_HOOK_MEM_WRITE, hw)]
        if arch == 'arm':
            uc.reg_write(UC_ARM_REG_SP, 0x201FF000)
            uc.reg_write(UC_ARM_REG_LR, STOP | 1)
            uc.emu_start(syms['main_loop'] | 1, STOP)
        else:
            uc.reg_write(UC_RISCV_REG_SP, 0x201FF000)
            uc.reg_write(UC_RISCV_REG_RA, STOP)
            uc.emu_start(syms['main_loop'], STOP)
        if count:
            for x in h:
                uc.hook_del(x)
        res = struct.unpack('<I', uc.mem_read(syms['RESULT'], 4))[0]
        out.append((sel, n[0], n[1], n[2], res))
    return out


if __name__ == '__main__':
    arch, elf = sys.argv[1:3]
    for s in map(int, sys.argv[3:]):
        seq = [(s - 1, False), (s, True)] if s % 10 == 4 else [(s, True)]
        r = session(arch, elf, seq)[-1]
        print(*r, flush=True)
