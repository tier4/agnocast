pan.c: main.pml
	rm -f pan.* *.trail pan *.tmp
	spin -a $<

pan: pan.c
	gcc -O3 -DCOLLAPSE -DVECTORSZ=5000 -DNFAIR=3 -o $@ $<

run: pan
	rm -f *.trail
	./pan -a -n -m30000

trail:
	clear
	spin -t main.pml

clean:
	rm -f pan.* *.trail pan *.tmp
