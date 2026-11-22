FROM --platform=linux/amd64 python:3.12-slim

RUN apt-get update \
    && apt-get install -y --no-install-recommends g++ \
    && rm -rf /var/lib/apt/lists/* \
    && pip install --no-cache-dir numpy pyarrow

WORKDIR /app
COPY pipeline.cpp run.py /app/

RUN g++ -O3 -std=c++20 -pthread /app/pipeline.cpp -o /app/pipeline \
    && chmod 755 /app/pipeline

USER 1000
ENTRYPOINT ["python3", "/app/run.py"]