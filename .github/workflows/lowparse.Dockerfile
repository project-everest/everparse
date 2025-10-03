ARG base_image
FROM $base_image

# Files will be overwritten
ADD --chown=test:test ./ /mnt/everparse/

ARG CI_THREADS

RUN ADMIT=1 make -j"$(if test -z "$CI_THREADS" ; then nproc ; else echo $CI_THREADS ; fi)" lowparse
