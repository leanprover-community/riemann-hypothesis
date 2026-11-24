module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

def PrismaticDieudonneAt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : Prop :=
  ∃ (M : PDivGroup p O → ModuleCat.{0} (Ainf p O))
    (map : ∀ G H : PDivGroup p O, (G ⟶ H) →+ (M H →ₗ[Ainf p O] M G))
    (φ : ∀ G, M G →ₛₗ[(frobenius : Ainf p O →+* Ainf p O)] M G)
    (lie : ∀ G, M G →ₛₗ[fontaineTheta O p] G.dual.Lie)
    (dR : ∀ G, M G →ₛₗ[fontaineTheta O p] G.RigExt),
    (∀ G, Module.Free (Ainf p O) (M G) ∧ Module.Finite (Ainf p O) (M G) ∧
      Module.finrank (Ainf p O) (M G) = G.height ∧
      Function.Injective (φ G) ∧ (∀ m, ∃ n, φ G n = frobenius (xi ε) • m) ∧
      Module.Projective O G.dual.Lie ∧ Function.Surjective (lie G) ∧
      (∀ m, lie G m = 0 ↔ ∃ n, φ G m = frobenius (xi ε) • n) ∧
      Function.Surjective (dR G) ∧ (∀ m, dR G m = 0 ↔ ∃ n, m = xi ε • n) ∧
      map G G (𝟙 G) = LinearMap.id) ∧
    (∀ (G H K : PDivGroup p O) (f : G ⟶ H) (g : H ⟶ K),
      map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M H),
      map G H f (φ H m) = φ G (map G H f m) ∧
      lie G (map G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie H m) ∧
      dR G (map G H f m) = rigExtMap f (dR H m)) ∧
    (∀ G H : PDivGroup p O, Function.Injective (map G H) ∧
      ∀ u : M H →ₗ[Ainf p O] M G, (∀ m, u (φ H m) = φ G (u m)) → ∃ f, map G H f = u) ∧
    ∃ (l : M (PDivGroup.mu p O)) (e : M (const p O)),
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ l) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ e) ∧
      φ _ l = frobenius (xi ε) • l ∧ φ _ e = e ∧
      map _ _ (epsHom (zeta ε) hε.zeta_zero (zeta_succ_pow ε)) l = Sandwich.mu ε • e

def PrismaticDieudonne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [NormedAlgebra ℚ_[p] C]
    [CompleteSpace C] [IsAlgClosed C] (O : Type) [CommRing O] [Algebra O C],
    IsIntegers O C →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
      (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), PrismaticDieudonneAt hε

end GlobalTheory.Published
