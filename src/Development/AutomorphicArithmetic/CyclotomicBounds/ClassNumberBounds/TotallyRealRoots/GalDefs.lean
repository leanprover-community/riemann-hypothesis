module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace KStar.TotallyRealRoots

noncomputable def eps (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] :
    Gal(AlgebraicClosure E/E) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (AlgebraicClosure E) l).comp
    (MulSemiringAction.toRingAut Gal(AlgebraicClosure E/E) (AlgebraicClosure E))

noncomputable def galImage (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] : Subgroup ℤ_[l]ˣ :=
  (eps l E).range

noncomputable def nuGal (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] (tr : ℕ) : ℕ∞ :=
  ⨅ g : Gal(AlgebraicClosure E/E),
    emultiplicity (l : ℤ_[l]) (((eps l E g : ℤ_[l]ˣ) : ℤ_[l]) ^ tr - 1)

theorem nuGal_eq_nu (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] (tr : ℕ) :
    nuGal l E tr = nu l (galImage l E) tr := by
  unfold nuGal nu nuStar galImage
  rw [iInf, Set.image_image]
  congr 1
  ext x
  simp [MonoidHom.coe_range]

noncomputable def adjoinRoots (E : Type*) [Field E] (m : ℕ) :
    IntermediateField E (AlgebraicClosure E) :=
  IntermediateField.adjoin E {ζ : AlgebraicClosure E | ζ ^ m = 1}

noncomputable def fieldSubgroup (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) : Subgroup (ZMod N)ˣ :=
  E.fixingSubgroup.map (IsCyclotomicExtension.Rat.galEquivZMod N K).toMonoidHom

end KStar.TotallyRealRoots
