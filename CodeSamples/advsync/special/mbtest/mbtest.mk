. mbtest.files

for i in $FILES
do
	cc -g -o $i $i.c -lpthread
done
