/* One RAM region, loaded as a whole by the emulator (bench/emu/run.py); no flash, no vector table. */
ENTRY(_reset)
MEMORY { RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 0x1FF000 }
_stack_top = ORIGIN(RAM) + LENGTH(RAM);
SECTIONS {
  .text : { KEEP(*(.text._reset)) *(.text .text.*) } > RAM
  .rodata : { *(.rodata .rodata.*) } > RAM
  .data : { *(.data .data.*) } > RAM
  .bss (NOLOAD) : { *(.bss .bss.*) *(COMMON) } > RAM
  /DISCARD/ : { *(.ARM.exidx*) *(.ARM.attributes) *(.riscv.attributes) *(.comment) *(.vectors) }
}
