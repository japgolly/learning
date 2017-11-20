#!/usr/bin/bash

url=https://gist.github.com/japgolly/06a1dca864feb7202376127066eccd19.js
f=$(basename $url)

dir=/tmp/${f%.js}
mkdir -p $dir
cd $dir || exit 1
echo "> $(pwd)"

bodyjs=body.js
output=output.html
rm -f $bodyjs $output

[ -e $f ] || curl -O $url
[ -e $f ] || exit 1

css_url="$(head -1 $f | perl -pe 's/.+"(https.+?)".+/$1/' | grep '^https')"
[ -z "$css_url" ] && echo "CSS not found" && exit 1
css_file="$(basename "$css_url")"

[ -e "$css_file" ] || curl -O "$css_url"
[ -e "$css_file" ] || exit 1

bodyjs=body.js
sed 1d $f | perl -pe 's/^document.write/console.log/' > $bodyjs || exit 1
[ -z "$(grep '^console' $bodyjs)" ] && echo "Body JS changed" && exit 1

echo "<style>
$(cat $css_file)
.gist .gist-file {border:none}
.gist .gist-data {border-bottom:none}
.gist .markdown-body .highlight pre, .gist .markdown-body pre {font-size:0.85rem}
</style>
" > $output
node $bodyjs >> $output

perl -pi -e 'undef $/; s/<div class="gist-meta">(?:.|\n)+?<\/div>//' $output
perl -pi -e 's/gist/goost/g' $output

echo "Done: $dir/$output"
