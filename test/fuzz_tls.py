import socket, os, random, struct, time, sys
PORT=int(sys.argv[1]) if len(sys.argv)>1 else 18444
def send(data, wait=0.0):
    try:
        s=socket.create_connection(("127.0.0.1",PORT),timeout=0.3); s.sendall(data)
        s.settimeout(0.03)
        try: s.recv(65536)
        except Exception: pass
        s.close()
    except Exception as e: pass
# Capture a real ClientHello from openssl to mutate
import subprocess
def real_ch():
    srv=socket.socket(); srv.bind(("127.0.0.1",0)); srv.listen(1); p=srv.getsockname()[1]
    pr=subprocess.Popen(["openssl","s_client","-connect",f"127.0.0.1:{p}","-tls1_3","-servername","x","-alpn","h2,http/1.1"],stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    c,_=srv.accept(); d=c.recv(65536); pr.kill(); c.close(); srv.close(); return d
ch=real_ch(); print("captured ClientHello record:",len(ch),"bytes")
random.seed(1); n=0
for it in range(3000):
    m=bytearray(ch)
    k=random.choice([1,1,2,4,8])
    for _ in range(k): m[random.randrange(len(m))]=random.randrange(256)
    if random.random()<0.3: m=m[:random.randrange(1,len(m))]
    if random.random()<0.1: m+=os.urandom(random.randrange(1,64))
    send(bytes(m)); n+=1
for it in range(500): send(os.urandom(random.randrange(1,3000))); n+=1
# valid record header, random body, all lengths/types
for t in (20,21,22,23,24,0,255):
    for l in (0,1,2,4,16,17,36,100,4100,16640,16641,60000):
        send(bytes([t,3,3])+struct.pack(">H",l&0xffff)+os.urandom(min(l,3000))); n+=1
print("sent",n,"malformed connections")
