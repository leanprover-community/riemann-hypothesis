module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.Pst TensorProduct Module Matrix CrystallineSemistableComparison
open GlobalTheory.GalV (HTower)

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.Int.Geo UpperTheory.Gal.Seam

def CongBC : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (L : Type) [Field L]
    (H : HTower E) (θ : H.Γ → L) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∀ (n : ℕ) (ϑ : ℕ → L), CongAt H θ w n ϑ →
    ∀ (A : ValuationSubring Ω), IsPlaceOver A w → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw →
      ∃ (_ : IsDomain ↥(OK l Bw.Kw.1)) (_ : IsDiscreteValuationRing ↥(OK l Bw.Kw.1)), 0 < resDeg l w ∧ normV w = l ^ resDeg l w ∧
        Nat.card (IsLocalRing.ResidueField ↥(OK l Bw.Kw.1)) = l ^ resDeg l w ∧
        ∃ C : Cover (bcAlong H (kOf Bw)) θ ↥(OK l Bw.Kw.1), C.Onto ∧ C.Cong l (resDeg l w) n ϑ

def CrysCopy : Prop := SmoothModelCrystalline → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
  ∀ (K : FinExt l) (M : Model l K.1), M.Sm → ∀ (j a : ℕ) (b : Basis (Fin a) ℚ_[l] (M.V j)),
    ∃ ρ : Representation ℚ_[l] ↥(GK K) (Fin a → ℚ_[l]), (∀ g v, ρ g (b.equivFun v) = b.equivFun (M.act j g v)) ∧ IsCrys (P.PD K) ρ

def GeoLoc : Prop := Br.FinAll → SmoothModelCrystalline → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
  ∀ (K : FinExt l) [IsDomain ↥(OK l K.1)] [IsDiscreteValuationRing ↥(OK l K.1)] (f : ℕ), 0 < f →
    Nat.card (IsLocalRing.ResidueField ↥(OK l K.1)) = l ^ f → ∀ (H : HTower ↥K.1) (θ : H.Γ → Om l), Nice H →
    ∀ (C : Cover H θ ↥(OK l K.1)), C.Onto → ∀ (n : ℕ) (ϑ : ℕ → Om l), C.Cong l f n ϑ →
    ∀ (a : ℕ) (ρ₁ : (PadicAlgCl l ≃ₐ[↥K.1] PadicAlgCl l) →* GL (Fin a) (Om l)), IsMat l H (PadicAlgCl l) (Om l) θ ρ₁ →
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℚ_[l] V) (_ : Module.Finite ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V)
      (T : ℕ → End ℚ_[l] V) (b : (Fin a → Om l) →ₗ[Om l] Om l ⊗[ℚ_[l]] V), IsCrys (P.PD K) ρ ∧ AnnD (σCr P K) (ψCr P f) (l ^ f) n ρ T ∧
      Function.Injective b ∧ (∀ (g : ↥(GK K)) x, b ((ρ₁ (IntermediateField.fixingSubgroupEquiv K.1 g) : Matrix (Fin a) (Fin a) (Om l)) *ᵥ x) =
        (ρ g).baseChange (Om l) (b x)) ∧ ∀ j ≤ n, ∀ x, (T j).baseChange (Om l) (b x) = ϑ j • b x

end UpperTheory.Ru.crystallineComparison
