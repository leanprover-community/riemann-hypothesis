module

public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
public import Formalism.LocalToGlobal.HermitianColumns.TiedQC

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def clsCast (D : D7) (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.cls i ≃ (D.chTw u D.what₂.mu0).cls i :=
  Equiv.cast (congrArg (fun C => C.cls i) (D.memberColumns_twistedChain_base u).symm)

def yCast (D : D7) (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.Y i ≃ (D.chTw u D.what₂.mu0).Y i :=
  Equiv.cast (congrArg (fun C => C.Y i) (D.memberColumns_twistedChain_base u).symm)

structure TwChMu0 {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ) : Prop where
  eY : ∀ u i hi, T.eY u D.what₂.mu0 i hi = yCast D u i
  eCls0 : ∀ u, T.eCls0 u D.what₂.mu0 = clsCast D u 0

end Formalism.L2.Herm

end
