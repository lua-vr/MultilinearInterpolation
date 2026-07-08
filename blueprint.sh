cleanup() { kill "$SERVER_PID" 2>/dev/null || true; }
trap cleanup EXIT

(cd _out/html-multi && uvx reloadserver -w) >/dev/null 2>&1 &
SERVER_PID=$!

lake exe blueprint-gen;

while inotifywait -r --exclude "_out/|.lake/|.git/|.jj/" -e close_write .; do
    lake exe blueprint-gen;
    curl -X POST localhost:8000/api-reloadserver/trigger-reload;
done
