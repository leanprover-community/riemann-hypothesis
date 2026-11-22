module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX
public import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.PeriodIntegrals.KFinSmooth
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianLattices.StatementMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.PhMeasCore
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLand
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.LitS

section Reexports

abbrev KFinSmooth : Prop := Formalism.MainNotions.DiscreteSeriesInnerProducts.KFinSmooth

theorem kFinSmooth_pi (h : KFinSmooth) : PI.KFinSmooth := by
  intro k r ε lam H _ _ _ σ _ hσ v hv
  exact h k r ε lam H σ hσ v hv

end Reexports

section RealPlaces

open scoped InnerProductSpace Matrix

def thetaJ {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε)

def dsigC {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  PI.PhMeasCore.dsig σ ((1 / 2 : ℂ) • (Y + thetaJ ε Y)) v +
    Complex.I • PI.PhMeasCore.dsig σ ((1 / (2 * Complex.I)) • (Y - thetaJ ε Y)) v

def dsigCW {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | Y :: w, v => dsigC ε σ Y (dsigCW ε σ w v)

def unitM {n : ℕ} (ab : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.single ab.1 ab.2 1

def Egl (n : ℕ) : Fin n → Fin n → FreeAlgebra ℂ (Fin n × Fin n) := fun a b => FreeAlgebra.ι ℂ (a, b)

def actU {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : H) : H :=
  Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff
    fun (w : FreeMonoid (Fin n × Fin n)) (c : ℂ) => c • dsigCW ε σ (w.toList.map unitM) v

end RealPlaces

section BesselPart

open Matrix
open scoped InnerProductSpace ContDiff

section BesselMultOne

open Formalism.MainNotions.S

theorem psi_eq_psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Formalism.QuantumDeterminants.psi k r z c = psiGen k r z (fun _ => c) := by
  funext g
  simp only [Formalism.QuantumDeterminants.psi, psiGen, Formalism.QuantumDeterminants.ell, ellA, Finset.mul_sum]

end BesselMultOne

end BesselPart

section GlobalHyps

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

end Herm

end GlobalHyps

section FiniteGroups

open Finset Matrix MeasureTheory

end FiniteGroups

section TextTau

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace Size

variable (I : Formalism.MainNotions.S.AutInst)

def latSet (x : I.GA) : Set (Fin I.n → I.E) :=
  {u | (I.fmat x.2⁻¹) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf}

def coordV (x : I.GA) (v : InfinitePlace I.F) (u : Fin I.n → I.E) : Fin I.n → ℂ :=
  (Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (u i))

def gramV (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) : Matrix (Fin j) (Fin j) ℂ :=
  fun a c => ∑ i, star (coordV I x v (b a) i) * coordV I x v (b c) i

structure Sub (x : I.GA) where
  j : ℕ
  j_pos : 1 ≤ j
  b : Fin j → Fin I.n → I.E
  b_ind : LinearIndependent I.E b
  B : Submodule (𝓞 I.E) (Fin I.n → I.E)
  B_lat : (B : Set (Fin I.n → I.E)) ⊆ latSet I x
  b_mem : ∀ a, b a ∈ B
  B_span : (B : Set (Fin I.n → I.E)) ⊆ Submodule.span I.E (Set.range b)

def ht {x : I.GA} (s : Sub I x) : ℝ :=
  (∏ v, (gramV I x v s.b).det.re) /
    (Nat.card (s.B ⧸ (Submodule.span (𝓞 I.E) (Set.range s.b)).comap s.B.subtype) : ℝ)

def size {x : I.GA} (s : Sub I x) : ℝ := ht I s ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)))

def tau1 (x : I.GA) : ℝ := min (1 / 2) (⨅ s : Sub I x, size I s)

end Size

def ReductionTau : Prop :=
  ∀ I : Formalism.MainNotions.S.AutInst, 1 ≤ I.n →
    Continuous (Size.tau1 I) ∧ ∀ x : I.GA, 0 < Size.tau1 I x ∧ Size.tau1 I x ≤ 1 / 2

end TextTau

section SpectralGap₂

open Finset Matrix MeasureTheory

section GapStatementAlt

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end GapStatementAlt

end SpectralGap₂

section BesselNVPart

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end BesselNVPart

end Formalism.L2.SG.LitS
