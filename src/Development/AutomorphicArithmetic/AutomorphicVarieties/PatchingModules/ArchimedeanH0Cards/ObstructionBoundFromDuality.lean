module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W

namespace UpperTheory.V.Pa.B2

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} (x : NP G0.frame n)
  (X : Type) [CommRing X] [Algebra x.A X]

structure IsOd (D : Dat x.A (plOf G)) where
  e : D.M.X ≃ₗ[x.A] Od x.A X n x.a
  act : ∀ (g : G.G₀) m, (e (D.M.ρ g m) : Matrix (Fin n) (Fin n) X) = x.ρX X (h.p₀ g) * e m * x.ρX X (h.p₀ g⁻¹)
  actc : ∀ m, (e (D.M.ρ G.c m) : Matrix (Fin n) (Fin n) X) = -(e m : Matrix (Fin n) (Fin n) X)ᵀ
  kerV : ∀ v m, D.π (.inl v) m = 0 ↔ ∀ i j, j < i → (x.wiX X v * (e m : Matrix (Fin n) (Fin n) X) * x.wX X v) i j = 0
  kerU : ∀ u, Function.Injective (D.π (.inr u))

variable {h x X} {X' : Type} [CommRing X'] [Algebra x.A X'] {D D' : Dat x.A (plOf G)}

def Induced (o : IsOd h x X D) (o' : IsOd h x X' D') (u : X →ₗ[x.A] X') (f : D.Hom D') : Prop :=
  ∀ m, (o'.e (f.f m) : Matrix (Fin n) (Fin n) X') = (o.e m : Matrix (Fin n) (Fin n) X).map u

def ObstructionBoundFromDuality : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x)
    (al : Fin T.q → Fin n → x.A) (d : ℕ), l ≠ 2 → (∃ dv, CohAx G0 d dv) → (∀ N, ∃ dv, CohAx (T.GN N) d dv) →
    (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → T.Eig x al → T.B2 k

end UpperTheory.V.Pa.B2
