module

public import Development.EtaleCohomology.DivisorCycles.CycleCount
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

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.StructPf
open LateralTheory.DivDb

theorem deg_img {Γ C : Type} [Group Γ] [Field C] {N n : ℕ} (ρ : Γ →* GL (Fin N) C)
    (h : ∀ g, Deg n (ρ g : Mat C N)) : ∀ x ∈ (img ρ ⊤ : Submonoid (Mat C N)), Deg n x := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := Submonoid.mem_map.mp hx
  exact h g

theorem Struct_of (hTanDeg : TanDeg) (hProj : Proj) (hTanLie : TanLie) (hGrade : Grade)
    (hDiag : DiagScalar) (hAlg : AlgStruct) (hEnv : EnvStab) (hSemis : Semis) : Struct := by
  intro Γ C _ _ _ _ N n ρ X e hSS hdeg hX hLac hroots

  have hdegL : ∀ Y ∈ lie ρ, Deg n Y := (hTanDeg C N n (img ρ ⊤) (deg_img ρ hdeg)).2
  have hinj : Function.Injective e := isLac_inj hLac

  obtain ⟨p, hSys, hXeq, hadj⟩ := hProj C N n X e hinj (hdegL X hX) hroots
  have hbr : ∀ Y ∈ lie ρ, ∀ Z ∈ lie ρ, Y * Z - Z * Y ∈ lie ρ := hTanLie C N (img ρ ⊤)

  have hoff : ∀ Y ∈ lie ρ, ∀ i j, i ≠ j → p i * Y * p j ∈ lie ρ :=
    hGrade C N n p e (lie ρ) hSys hLac (fun Y hY => by rw [← hXeq]; exact hbr X hX Y hY)

  have hdiag : ∀ Y ∈ lie ρ, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i :=
    fun Y hY hc => hDiag C N n p e Y hSys hinj hc (fun s => by
      rw [← hXeq]; exact hdegL _ ((lie ρ).add_mem ((lie ρ).smul_mem s hY) hX))
  have hA := hAlg C N n p (lie ρ) hSys hbr hoff hdiag
  obtain ⟨hNormd, hKeeps⟩ := hEnv Γ C N ρ
  refine ⟨p, hSys, by rw [← hXeq]; exact hX, ⟨fun i => ?_, fun a ha i => (hA a ha).2 i⟩,
    hSemis Γ C N ρ (env ρ) hSS hNormd hKeeps, hNormd, hKeeps, fun a ha i j hij => (hA a ha).1 i j hij⟩
  exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hX) (hadj i)

end LateralTheory.DivDb.StructPf
