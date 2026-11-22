module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
public import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints

@[expose] public section

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Forms Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie
open NumberField IsDedekindDomain Matrix GlobalTheory.BigTop GlobalTheory.Mem.R3 GlobalTheory.Core.Rk.Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Conj

variable {ι : Type} [Fintype ι] {n : ℕ}

end Conj

variable {D : D7}

def LevIs {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad)
    (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (∀ h, h ∈ J ↔ ∃ κ : S.U, HasMat h κ.1) ∧ ∀ h (κ : S.U), HasMat h κ.1 → χ h = star ((S.chi κ : ℂˣ) : ℂ)

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable {R}

end Real

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

variable (Cs : ColsTiedSym D) (tw : SymmetricTwistedColumnsAtPrimes p.Tp Cs ex.tw)

variable {p Cs tw} {co : Coord p} {e₀ e₀' : ∀ u, (D.mem u).P.Mt ≃ₗ[ℂ] D.what₂.Amb D.what₂.mu0}
  {e e' : ∀ u μ, (D.PTw u μ).Mt ≃ₗ[ℂ] D.what₂.Amb μ}

end Point

end GlobalTheory.EX

end
