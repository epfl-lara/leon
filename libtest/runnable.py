import sys
import re

fileName = sys.argv[1]
f = open("../leon.out/" + fileName, "r")
fw = open("src/main/scala/benchmark/" + fileName, "w")
d = f.readlines()
f.close()

fw.write("package " + fileName[:-6] + "\n\n")

def removeUnnecessaryClass(d):
	classes = []
	def get_trailing_number(s):
	    m = re.search(r'\d+$', s)
	    return int(m.group()) if m else None
	
	newd = [i.strip() for i in d]
	for i in newd:
		words = i.split(" ")
		if(len(words) < 3):
			continue
		if(words[1] == "class"):
			classname = words[2].partition("(")[0].partition("[")[0]
			number = get_trailing_number(classname)
			if(number != None):
				base = classname[:-1*len(str(number))]
				for i in range(number):
					if(i == 0):
						if base in classes:
							classes.remove(base)
					else:
						if (base + str(i)) in classes:
							classes.remove(base + str(i))
			classes.append(classname)

	def notrepetitiveclass(i):
		words = i.strip().split(" ")
		if(len(words) < 3):
			return True
		if(words[1] != "class"):
			return True
		elif(words[2] == "List()"):
			return False
		elif(words[2].partition("(")[0].partition("[")[0] not in classes):
			return False
		else:
			return True

	oldd = [i for i in d if notrepetitiveclass(i)]
	return oldd

def fixLookupAndUpdate(d):
	def fixString(s):
		news = re.sub(r'\*\*\*\* lookup(.*?)\[',"lookup[",s)
		news = re.sub(r'\*\*\*\* update(.*?)\[',"update[",news)
		return news
	newd = [fixString(i) for i in d]
	return newd

def fixListImport(d):
	newd = d
	if "import leon.collection._" not in d:
		newd = ["import leon.collection._\n"] + newd
	return newd

d = fixLookupAndUpdate(removeUnnecessaryClass(fixListImport(d)))

for i in d:
	fw.write(i)
fw.truncate()
fw.close()
