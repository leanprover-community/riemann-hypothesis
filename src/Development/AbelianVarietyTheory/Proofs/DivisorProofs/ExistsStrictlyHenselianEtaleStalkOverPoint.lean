module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianIndEtaleOverPrime
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.exists_isStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom →
    ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S)
      (g : Over.mk s ⟶ U), _root_.GlobalTheory.EtC.IsStalk O s ∧ ∃ v, g.left v = u := by
  intro S U hU u
  let 𝒰 := U.left.affineOpenCover
  obtain ⟨y, hy⟩ := 𝒰.covers u
  let R : CommRingCat := 𝒰.X (𝒰.idx u)
  let f : Spec R ⟶ U.left := 𝒰.f (𝒰.idx u)
  haveI : IsOpenImmersion f := 𝒰.map_prop _
  haveI := hU
  let j : Spec R ⟶ S := f ≫ U.hom
  let y' : Spec R := y
  haveI := y'.isPrime
  obtain ⟨O, hO, hAO, hloc, hsh, hind, hcomap⟩ :=
    _root_.GlobalTheory.StrictHensPrime.exists_sh_indEt R y'.asIdeal
  let φ : Spec (CommRingCat.of O) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R O))
  refine ⟨O, hO, φ ≫ j, Over.homMk (φ ≫ f) (by simp [j]),
    ⟨hsh, R, inferInstance, hAO, j, inferInstance, hind, rfl⟩, IsLocalRing.closedPoint O, ?_⟩
  have hφ : φ (IsLocalRing.closedPoint O) = y' := by
    apply PrimeSpectrum.ext
    rw [← hcomap]
    rfl
  show (φ ≫ f) (IsLocalRing.closedPoint O) = u
  change f (φ (IsLocalRing.closedPoint O)) = u
  rw [hφ]
  exact hy

end GlobalTheory.EtC
