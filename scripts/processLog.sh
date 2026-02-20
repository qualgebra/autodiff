#sh

sed -i 'N;s/\n,/,/g' log.txt
sed -i '/warning/d' log.txt
sed -i '/EnvExts/d' log.txt
sed -i '/Built/d' log.txt
sed -i '/^$/d' log.txt

