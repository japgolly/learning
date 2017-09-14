# Serve

../reveal-md scalajs-react.md -w

# Make PDF

docker run --rm --net=host -v `pwd`:/slides astefanutti/decktape reveal -s 1920x1080 http://localhost:1948/scalajs-react.md as.pdf

# Make static site

perl -pi -e 's!assets/!!g' scalajs-react.md
../reveal-md scalajs-react.md -S

