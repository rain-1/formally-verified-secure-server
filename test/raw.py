import socket, sys, time
def tx(data, wait=0.3, port=18080):
    s = socket.create_connection(("127.0.0.1", port)); s.settimeout(1.5)
    s.sendall(data); time.sleep(wait)
    out = b""
    try:
        while True:
            d = s.recv(65536)
            if not d: break
            out += d
    except socket.timeout: pass
    s.close(); return out
def status(o): return o.split(b"\r\n",1)[0].decode(errors="replace") if o else "(closed, no response)"
H = b"Host: x\r\n"
cases = {
 "good":                 b"GET / HTTP/1.1\r\n"+H+b"\r\n",
 "no host":              b"GET / HTTP/1.1\r\n\r\n",
 "two hosts":            b"GET / HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n",
 "http/1.0":             b"GET / HTTP/1.0\r\n"+H+b"\r\n",
 "CL:5 body (smuggle)":  b"GET / HTTP/1.1\r\n"+H+b"Content-Length: 5\r\n\r\nhello",
 "CL:0 ok":              b"GET / HTTP/1.1\r\n"+H+b"Content-Length: 0\r\n\r\n",
 "TE chunked":           b"GET / HTTP/1.1\r\n"+H+b"Transfer-Encoding: chunked\r\n\r\n0\r\n\r\n",
 "bare LF line ends":    b"GET / HTTP/1.1\nHost: x\n\n",
 "obs-fold":             b"GET / HTTP/1.1\r\nHost: x\r\n y\r\n\r\n",
 "NUL in header":        b"GET / HTTP/1.1\r\nHost: x\x00y\r\n\r\n",
 "space in target":      b"GET /a b HTTP/1.1\r\n"+H+b"\r\n",
 "absolute-form":        b"GET http://x/ HTTP/1.1\r\n"+H+b"\r\n",
 "lowercase method":     b"get / HTTP/1.1\r\n"+H+b"\r\n",
 "DELETE":               b"DELETE / HTTP/1.1\r\n"+H+b"\r\n",
 "garbage":              b"\x16\x03\x01\x02\x00\x01\x00\x01\xfc\x03\x03\r\n\r\n",
 "2 pipelined":          b"GET / HTTP/1.1\r\n"+H+b"\r\nGET /style.css HTTP/1.1\r\n"+H+b"Connection: close\r\n\r\n",
 "header >8k":           b"GET / HTTP/1.1\r\n"+H+b"X: "+b"a"*9000+b"\r\n\r\n",
 "target >2k":           b"GET /"+b"a"*3000+b" HTTP/1.1\r\n"+H+b"\r\n",
 "conn: close":          b"GET / HTTP/1.1\r\n"+H+b"Connection: Keep-Alive, CLOSE\r\n\r\n",
}
for k,v in cases.items():
    o = tx(v); print(f"{k:22s} {status(o)}   [{o.count(b'HTTP/1.1 ')} resp]")
# slow loris: send partial header then idle
s = socket.create_connection(("127.0.0.1",18080)); s.sendall(b"GET / HT"); s.settimeout(20)
t=time.time()
try: d=s.recv(10); print("slowloris: closed after %.0fs (recv=%r)"%(time.time()-t,d))
except Exception as e: print("slowloris: still open after 20s", e)
