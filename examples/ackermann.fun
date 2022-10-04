ack (Roll (), n) = Roll ((), n)
ack (Roll ((), m), Roll ()) = ack (m, Roll ((), Roll ()))
ack (Roll ((), m), Roll ((), n)) = ack (m, ack (Roll ((), m), n))