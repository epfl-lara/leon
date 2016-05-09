print("SET 1")
for i in range(10, 210, 10):
	print(str(i) + " " + str((703*i*i + 192)/64.0))
print("SET 2")
for i in range(10, 210, 10):
	print(str(i) + " " + str(4*i*i + 6*i + 3))
 

# set 1
# 64 * time <= 703 * (size(l) * size(l)) + 192
# set 2
# time <= (4 * (size(l) * size(l)) + 6 * size(l)) + 3
