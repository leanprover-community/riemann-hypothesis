module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.AvgData
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U

open PositivityTheory.RgUd.Form

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def GLEq {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (m : ℕ) (h : m + 1 ≤ N)
    (s : ℝ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ g v w, B (π (blkAt k (m + 1) N h g) v) (π (blkAt k (m + 1) N h g) w) =
    ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * B v w

def DerKer {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V)
    (m : ℕ) : Submodule ℂ V :=
  twKer π (derUnip k N (m + 1)) (derChar k ψ N (m + 1))

def Lvl {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V)
    (m : ℕ) (h : m + 2 ≤ N) (s : ℝ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  IsPsd B ∧ Kills ψ π (m + 2) B ∧ MirEq π (m + 1) h s B

def UAtom : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m N : ℕ) (h : m + 2 ≤ N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (s : ℝ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), Lvl k ψ π m h s B →
    ∃ B₀, IsAtom h π B B₀ ∧ IsPsd B₀ ∧ (∀ v, (B₀ v v).re ≤ (B v v).re) ∧ (∀ v ∈ DerKer k ψ π m, ∀ w, B₀ v w = 0) ∧
      GLEq k π m (by omega) s B₀ ∧ MirEq π (m + 1) h s B₀

def UDens : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m N : ℕ) (h : m + 2 ≤ N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (s : ℝ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), Lvl k ψ π m h s B →
    ∀ A₀, IsLat A₀ → ∃ B', IsDens ψ h π A₀ B B' ∧ IsPsd B' ∧ Kills ψ π (m + 1) B' ∧ MirEq π m (by omega) (s + 1) B' ∧
      (∀ v, B' v v = 0 → v ∈ twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) ⊔ LinearMap.ker B)

def USplit : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m N : ℕ) (h : m + 2 ≤ N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (s : ℝ) (B B₀ B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) A₀,
    Lvl k ψ π m h s B → IsLat A₀ → IsAtom h π B B₀ → IsDens ψ h π A₀ B B' →
    ((∀ v, B' v v = 0) → B₀ = B) ∧ ∀ c : ℂ, (∀ v w, B₀ v w = c * B v w) → (∃ v, B' v v ≠ 0) → c = 0

def ULift : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m N : ℕ) (h : m + 2 ≤ N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (s : ℝ) (B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) A₀,
    Lvl k ψ π m h s B → IsLat A₀ → IsDens ψ h π A₀ B B' → IsPsd C → Kills ψ π (m + 1) C → MirEq π m (by omega) (s + 1) C →
    (∀ v, (C v v).re ≤ (B' v v).re) →
    ∃ I, Lvl k ψ π m h s I ∧ (∀ v, (I v v).re ≤ (B v v).re) ∧ IsDens ψ h π A₀ I C ∧ IsAtom h π I 0

def UShell : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m N : ℕ) (h : m + 2 ≤ N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (s : ℝ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), Lvl k ψ π m h s B →
    IsAtom h π B 0 → ∀ (z : kˣ) (c : ℂ) (v : V), nabs k z < 1 →
      π (scalAt k (m + 1) N (by omega) z) v - c • v ∈ DerKer k ψ π m → v ∉ DerKer k ψ π m ⊔ LinearMap.ker B →
      ‖c‖ ^ 2 < nabs k z ^ (((m : ℝ) + 1) * s)

def UEig : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n i : ℕ) (π : GRep k (n + i)), IsSmooth π.ρ → π.ρ.IsIrreducible →
    ∀ (t : ℝ) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin n) k) W) (ω : kˣ →* ℂˣ), Nontrivial W →
      IsSubquotient σ ((derivB ψ i π).tw t).ρ → HasCentralChar σ ω → ∀ z : kˣ,
        ∃ x : (derivB ψ i π).V, x ≠ 0 ∧ ((derivB ψ i π).tw t).ρ (GeneralLinearGroup.scalar (Fin n) z) x = (ω z : ℂ) • x

def UAdm : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n i : ℕ) (π : GRep k (n + i)), IsSmooth π.ρ → π.ρ.IsIrreducible →
    IsAdmissible (derivB ψ i π).ρ

def UAsm : Prop :=
  UAtom k → UDens k → USplit k → ULift k → UShell k → UEig k → UAdm k → ThmB k → DerivTop k ∧ DerivPos k

end PositivityTheory.RgUd.Form.U
