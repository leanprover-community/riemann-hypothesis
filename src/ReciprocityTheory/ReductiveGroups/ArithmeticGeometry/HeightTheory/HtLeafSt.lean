module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightIntegralEstimates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option linter.unusedVariables false

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

namespace LeafSt

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)

def PlaceTrivialOrPositive : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p),
  (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∨
    (d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) ∧
      ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
        w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0)

def AdmissibleValuationPrimeUnique : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι),
  ∀ v : AddValuation (Ω c) (WithTop ℤ), d.admitted c v → IsTrivOn K v →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}.Subsingleton

def GeneratorMultiHomogeneous : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι),
  ∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p)

def places_over_la : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι),
  (d.PlOver la c).Finite ∧
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
        (d.fze h c w : ℤ) * ramIdx (K := K) (d.Wres c w) la) = d.delc c

def exists_generic : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1),
  (∃ x : Fin (d.N + 1) → K, ∀ c, d.wx x c ≠ 0) ∧
    (∃ ta' : ∀ c, A c, ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0)

end LeafSt

end ReciprocityTheory.ChartRestriction.G.T0
