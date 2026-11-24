module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
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

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

def CorrPull : Prop :=
  ∀ (l : ℕ) (S S' Y Y' : Scheme.{0}) (u : S' ⟶ S) (f : Y ⟶ S) (f' : Y' ⟶ S') (h : Y' ⟶ Y), IsPullback h f' f u →
    ∀ T : Corr l Y, T.r ≫ f = T.p ≫ f → ∃ (T' : Corr l Y') (g : T'.Z ⟶ T.Z),
      IsPullback T'.p g h T.p ∧ T'.r ≫ h = g ≫ T.r ∧ T'.r ≫ f' = T'.p ≫ f' ∧ T'.d = T.d

def PtIdBC : Prop :=
  ∀ (l q n : ℕ) (O O' : Type) [CommRing O] [CommRing O'] (σ : O →+* O'), σ.Flat → ∀ (ϖ : O) (ϖ' : O'),
    (∀ P : Ideal O', P.IsPrime → (σ ϖ ∈ P ↔ ϖ' ∈ P)) → (∀ a : O', a ^ q - a ∈ Ideal.span {ϖ'}) →
    ∀ (Y Y' : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of O)) (f' : Y' ⟶ Spec (CommRingCat.of O')) (h : Y' ⟶ Y),
    IsPullback h f' f (Spec.map (CommRingCat.ofHom σ)) → ∀ (T : Fin (n + 1) → Corr l Y) (T' : Fin (n + 1) → Corr l Y')
      (g : ∀ j, (T' j).Z ⟶ (T j).Z), (∀ j, IsPullback (T' j).p (g j) h (T j).p) → (∀ j, (T' j).r ≫ h = g j ≫ (T j).r) →
      (∀ j, (T' j).r ≫ f' = (T' j).p ≫ f') → PtId l q n (fn f ϖ) T → PtId l q n (fn f' ϖ') T'

def DvdOfNil : Prop :=
  ∀ (K W : Type) [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W] [Module.Finite K W] (M : End K W) (s : Multiset K) (u : K),
    u ≠ 0 → IsNilpotent (Polynomial.aeval M (Polynomial.C u * rootPol s)) → ∃ m : ℕ, M.charpoly ∣ rootPol s ^ m

def PhiKOfNil : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (a : ℕ)
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (LL : FinExt l) (r' : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL.1),
    IsModel Bw r LL r' → Bw.IsCrysE P LL r' → ∀ (Q : Polynomial ↥LL.1), NilD (σSt P Bw.Kw) (ψSt P (resDeg l w)) (Bw.repE LL r') Q →
    ∀ (s : Multiset ℂ) (u : ℂ), u ≠ 0 → Q.map (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) = Polynomial.C u * rootPol s →
    ∃ g : ↥(Weil h), deg g = -1 ∧ ∃ m : ℕ, (wdAt P ι Bw h hj r).charPol g ∣ rootPol s ^ m

end UpperTheory.Gal.crystallineComparison
