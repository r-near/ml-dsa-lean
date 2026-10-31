#!/usr/bin/env python3
"""Print the lowest-numbered CPU (>= 4) that has been idle (> 98.5%) for 2 s together with all of its SMT siblings;
fall back to 10 (the CPU used by docs/performance-baseline.md)."""
import time


def snap():
    d = {}
    for line in open('/proc/stat'):
        if line.startswith('cpu') and line[3].isdigit():
            f = line.split()
            v = list(map(int, f[1:]))
            d[int(f[0][3:])] = (v[3] + v[4], sum(v))
    return d


a = snap()
time.sleep(2)
b = snap()
idle = {c: (b[c][0] - a[c][0]) / max(1, b[c][1] - a[c][1]) for c in a}
for c in sorted(idle):
    sib = [int(x) for x in open(f'/sys/devices/system/cpu/cpu{c}/topology/thread_siblings_list').read().replace('-', ',').split(',')]
    if c >= 4 and idle[c] > 0.985 and all(idle.get(s, 0) > 0.985 for s in sib):
        print(c)
        break
else:
    print(10)
