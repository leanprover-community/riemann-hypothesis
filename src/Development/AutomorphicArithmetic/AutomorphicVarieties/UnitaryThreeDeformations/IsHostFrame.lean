module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3 IsLocalRing

namespace UpperTheory.V.UnitaryThreeInertia

structure HostData (l e : ℕ) {O : Type} [CommRing O] {N : ℕ} (ψ : DirichletCharacter O N) (o₁ : ℕ) : Prop where
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  N_even : Even N
  par : PsiEven e ψ
  o_pos : 1 ≤ o₁
  ord : ∀ r : ℕ, r.Prime → r ≠ 2 → comp r (th0 l ψ) ^ (2 * o₁) = 1
  R : ∀ v ∈ Tb l ψ, 8 * o₁ * v ^ 2 < 2 ^ c2 ψ
  four_le : 4 ≤ c2 ψ

abbrev Pl : Type := HeightOneSpectrum (𝓞 ℚ)

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

def eta4 : G ℚ Ω →* ℤˣ := Chr.dirG ℚ Ω (ZMod.χ₄ : DirichletCharacter ℤ 4)

abbrev Gam (S : Finset Pl) : Type := GS Ω (S : Set Pl)

variable {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N]

structure IsHostFrame (e : ℕ) (ψ : DirichletCharacter c.O N) (S : Finset Pl) (A : S → ValuationSubring Ω)
    (F : Frame c.O (G ℚ Ω) (Gam Ω S) S) : Prop where
  mem : ∀ v : Pl, v ∈ S ↔ ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  isOver : ∀ v, IsPlaceOver (A v) v.1
  π : F.π = toGS Ω _
  η : F.η.comp F.π = eta4 Ω
  Ψ : F.Ψ.comp F.π = Chr.Psi l e (Chr.dirG ℚ Ω ψ)
  cc : ∃ σ : G ℚ Ω, IsCC σ ∧ F.π σ = F.c
  D : ∀ v, F.D v = Dec (F := ℚ) (A v)
  I : ∀ v, F.I v = Ine (F := ℚ) (A v)
  vl : ((l : ℕ) : 𝓞 ℚ) ∈ F.vl.1.asIdeal
  Sb : ∀ v, v ∈ F.Sb ↔ ∃ p ∈ HV.Sb l ψ, ((p : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal

def vl1 (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) : ℝ := -Real.log ‖x‖ / Real.log l

def XData (l : ℕ) {O : Type} [CommRing O] {N : ℕ} (ψ : DirichletCharacter O N) (q : ℕ) : Prop :=
  0 < q ∧ (th1 l ψ ^ 2).conductor ∣ q ∧ 2 * (l * q) * 4 ^ n0 l ψ ≤ 2 ^ c2 ψ

end UpperTheory.V.UnitaryThreeInertia

end
