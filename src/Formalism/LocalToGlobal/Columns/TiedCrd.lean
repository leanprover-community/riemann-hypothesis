module

public import Formalism.LocalToGlobal.Columns.WordFin
public import Formalism.LocalToGlobal.Columns.TiedCG

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

structure SpStd (B : ColBase) : Prop where
  X_on : ∀ i, i ≤ B.R.m → ∀ a b, (B.sp.X i).hT ((B.sp.X i).frame a) ((B.sp.X i).frame b) = if a = b then 1 else 0
  selfDual_span_frame_X : ∀ i, i ≤ B.R.m → (B.sp.X i).L0 = Submodule.span (𝓞 B.host.E) (Set.range (B.sp.X i).frame)
  P_on : ∀ a b, B.sp.X'.hT (B.sp.X'.frame a) (B.sp.X'.frame b) = if a = b then 1 else 0
  selfDual_span_frame_auxiliary : B.sp.X'.L0 = Submodule.span (𝓞 B.host.E) (Set.range B.sp.X'.frame)
  iX' : ∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b →
    B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b
  z : ∃ c : B.host.E, ∀ b : Fin (B.sp.X B.R.m).rank, (b : ℕ) + 1 = (B.sp.X B.R.m).rank → B.sp.z = c • (B.sp.X B.R.m).frame b

structure HostHyp (d : ColDat) : Prop where
  embE_φ₀ : d.what₂.embLL.comp d.embE = d.host.φ₀
  piT_K : ∀ u, (d.piT u : d.host.E) ∈ d.host.K
  piG_K : ∀ i, (d.piG i : d.host.E) ∈ d.host.K
  cond_eq : d.cond = d.host.QS * d.host.q * d.host.d
  val_eq : ∀ w (x : d.what₂.LL), x ≠ 0 → d.what₂.places.val w x = ((vAdd (d.plEq w) x : ℤ) : WithTop ℤ)

variable {d : ColDat} (a : ColArgs d)

end Formalism.L2.Col
