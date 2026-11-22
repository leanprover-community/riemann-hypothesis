module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CxTiesOf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses
public import Formalism.LocalToGlobal.IndefiniteReal.RealPins

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

section Alg

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}

def Anchored (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ)
    (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  ∀ u, ∃ p b : ℂ, p ≠ 0 ∧ b ≠ 0 ∧ ∀ t (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K),
    c u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) * b =
      p * ⟪sEE (V (X.Θ t (X.jR t (eV t F)))), (fc X.zs).Sp.Pu u ((U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def UnitAt (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  (∀ u t, c u t ≠ 0) ∧ ∀ u w (k : K), Bs.v0.embedding k = c u (X.μ w) / c u Bs.μ0 → vw w k = 0

end Alg

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

variable {W}

variable (W)

end GlobalTheory.MiTop

namespace GlobalTheory.MiTop

def PuNZ (D : D7) : Prop :=
  ∀ u, ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0

end GlobalTheory.MiTop

end
