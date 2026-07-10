import Rfc4648

def main : IO Unit :=
  IO.println (Rfc4648.Base64.encode "hi".toUTF8)
