#!/usr/bin/env python3

'''Test for AXFR-style IXFR'''

from dnstest.test import Test
import os

t = Test(tsig=False)

master = t.server("bind")
slave = t.server("knot")
zone = t.zone("xfr", storage=".")

t.link(zone, master, slave)

t.start()

serial = master.zone_wait(zone)

# update zone with small change
master.update_zonefile(zone, version=1)
master.reload()
master.zone_wait(zone, serial)
serial = slave.zone_wait(zone, serial)

t.xfr_diff(master, slave, zone)

# update zone with large change (3 messages worth)
filename = master.data_dir + zone[0].name + "zone.2"
f = open(filename, "w")
f.write(zone[0].name + " IN SOA . . 3 100 100 100 100\n")
f.write(zone[0].name + " IN NS smth\n")
f.write("smth IN A 1.2.3.4\n")
for i in range(2000):
    f.write("test" + str(i) + " TXT " + "test" * 16 + "\n")
f.close()
master.update_zonefile(zone, version=2)
os.remove(filename)

master.reload()
master.zone_wait(zone, serial)
slave.zone_wait(zone, serial)
t.xfr_diff(master, slave, zone)

t.stop()