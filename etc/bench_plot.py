#!/usr/bin/env python3

from bs4 import BeautifulSoup
import os
import sys
from matplotlib import pyplot as plt
import matplotlib
import re

matplotlib.rcParams["mathtext.fontset"] = "stix"
matplotlib.rcParams["font.family"] = "STIXGeneral"

# Filenames should be: name.something.xml -> name.png


def normalize_xml(xml_fnam):
    with open(xml_fnam, "r") as f:
        xml = f.read()
        xml = re.sub("&lt;", "<", xml)
    with open(xml_fnam, "w") as f:
        f.write(xml)


def xml_stdout_get(xml, name):
    try:
        return xml.find("StdOut").find(name)["value"]
    except (KeyError, TypeError):
        return None


def time_unit(Y):
    time_units = ("nanoseconds", "microseconds", "milliseconds", "seconds")
    index = 0

    while all(y > 1000 for y in Y) and index < len(time_units):
        index += 1
        Y = [y / 1000 for y in Y]
    return time_units[index], Y


def add_plot(xml_fnam):
    print("Reading {} . . .".format(xml_fnam))
    normalize_xml(xml_fnam)

    xml = BeautifulSoup(open(xml_fnam, "r"), "xml")
    results = xml.find_all("BenchmarkResults")

    # Benchmark labels must be the value that is the x-axis
    X = [int(x["name"]) for x in results]
    Y = [
        float(x.find("mean")["value"]) for x in results
    ]  # times in nanoseconds

    t, Y = time_unit(Y)
    title = xml_stdout_get(xml, "Title")
    xlabel = xml_stdout_get(xml, "XLabel")
    label = xml_stdout_get(xml, "Label")
    assert label is not None

    plt.plot(X, Y, "x", label=label)
    if title is not None:
        plt.title(title)
    if xlabel is not None:
        plt.xlabel(xlabel)
    plt.ylabel("Time in {}".format(t))
    plt.legend(loc="lower right")


from sys import argv

args = sys.argv[1:]
# TODO arg checks
for x in args:
    add_plot(x)
xml_fnam = args[0]
png_fnam = "".join(xml_fnam.split(".")[:-2]) + ".png"
print("Writing {} . . .".format(png_fnam))
plt.savefig(png_fnam, format="png", dpi=300)
sys.exit(0)
