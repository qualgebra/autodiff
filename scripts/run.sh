#sh

for (( i=$1 ; i<=$2; i++ ));
do	
    lake exec autodiff $i 2>> log.txt
done

