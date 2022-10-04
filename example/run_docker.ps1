docker run --rm -v $PWD:/pwd -d --name customeverparse -i customeverparse:everparse
docker exec -it customeverparse /bin/bash