#!/usr/bin/python3
infn = "supero-SEC-output"
srcfn = "sourcet"
tempfn = "/tmp/annotate"
outfn = "supero-SEC-output-annotated"
srcoutfn = "source-annotated"
outlines = []

def annotate(infn, outfn, wlast):
	outlines = []
	last=""
	with open(infn,"r") as infile:
		with open(outfn,"w") as outfile:
			text = infile.read()
			lines = text.splitlines()
			for line in lines:
				if (len(line) >= 2) and line[-2] == ';':
					ncycs = 0
					nbytes = 0
					words = line.split()
					for word in words:
						if word == "lsr;" or word == "ror;" or word == "clc;" or word == "sec;":
							ncycs += 2
							nbytes += 1
						elif word == "adc" or word == "sbc":
							ncycs += 3
							nbytes += 2
						elif word[0] == "{" or word == "rts;":
							pass
						elif word[0] == "#":
							ncycs -= 1
						else:
							print(word)
							print("huh?")
					if wlast:
						outlines.append(f"{ncycs} cycles, {nbytes} bytes: {line}")
					else:
						outlines.append(f"{last} {ncycs} cycles, {nbytes} bytes: {line}")
				else:
					last = line
					if wlast:
						outlines.append(line)
			outfile.write("\n".join(outlines))

def source2super(infn, outfn):
	outlines = []
	words = []
	with open(infn,"r") as infile:
		with open(outfn,"w") as outfile:
			text = infile.read()
			lines = text.splitlines()
			for line in lines:
				sline = line.strip()
				if len(sline) == 0:
					words.append("")
					outlines.append("; ".join(words))
					words=[]
				if "label" in sline or "comment" in sline or "insn" not in sline:
					outlines.append(line)
				else:
					start = line.index("}")
					end = line.rindex('"')
					word = line[start+1:end]
					words.append(word)
			outfile.write("\n".join(outlines))

for i in range(4):
	for j in range(4):
		inn = f"supero-output-dir/supero-out-{j}-{i}.txt"
		outn = f"supero-output-dir/annotated-{j}-{i}.txt"
		annotate(inn, outn, False)
source2super(srcfn, tempfn)
annotate(tempfn, srcoutfn, True)
