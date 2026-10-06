# The proofs of LAWS.bend. Each file under proofs/ proves a group of laws
# (`def Laws.<name>`) with its own lemmas. The gate:
#   bend PROOF.bend             ALL PROOFS CHECK once every law is proven
#   bend PROOF.bend --verdict   the same, rechecked by the BendTT kernel (Lean)
import Base
import ./LAWS.bend as Laws
import ./proofs/num.bend as P_num
import ./proofs/wire.bend as P_wire
import ./proofs/concrete.bend as P_concrete
import ./proofs/answer_conf.bend as P_answer_conf
import ./proofs/ip_frame.bend as P_ip_frame
import ./proofs/name.bend as P_name
import ./proofs/message.bend as P_message
