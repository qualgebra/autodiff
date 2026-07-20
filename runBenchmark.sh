#sh
rm -f log.txt
rm test*.txt
rm -f univ_domain.txt

echo "idx,input,size,depth,t1,t2,t3,t4" >> log.txt
./scripts/run.sh 1 3
./scripts/processLog.sh

grep 'domain := fun x => True,' *.txt >> univ_domain.txt
sed -i 's/test//g' univ_domain.txt
sed -i 's/\.txt.*//g' univ_domain.txt