# Serve

../reveal-md src/scalajs-react.md -w

# Make PDF

docker run --rm --net=host -v `pwd`:/slides astefanutti/decktape reveal -s 1920x1080 http://localhost:1948/src/scalajs-react.md as.pdf

