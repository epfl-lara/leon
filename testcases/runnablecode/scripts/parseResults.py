with open('results') as f:
    lines = f.readlines()

for result in lines:
	print(result.split(" ")[1] + " " + result.split(",")[-2])
