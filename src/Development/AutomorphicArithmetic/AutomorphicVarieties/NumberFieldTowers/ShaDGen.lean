module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DinfNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTors
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.shaDGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U V : Subgroup (G k Ω)) [U.Normal] (e : ℤ) (γ : G k Ω), IsClosed (U : Set (G k Ω)) → V ≤ U → IsGen l V γ →
        ShaD l N U V e = LinearMap.ker (dTw l N U e γ - 1) ∧ ShaD l N U V e = LinearMap.ker (dTw l N U e γ⁻¹ - 1) := by
  intro k Ω _ _ _ _ _ l hl N U V _ e γ hU hVU hγ
  have key : ∀ φ : Dinf l N U, dTw l N U e γ φ = φ → ∀ v ∈ V, dTw l N U e v φ = φ := by
    intro φ hφ v hv
    obtain ⟨n, hn⟩ := (dinfNil k Ω l N U hU φ.1 φ.2).1
    obtain ⟨r, hr⟩ := (dinfTors k Ω l N U).1 hU φ
    have hlev : ∀ w ∈ U, cycZ k Ω l w ∈ KStar.TotallyRealRoots.princ l (max n r) → dTw l N U e w φ = φ := by
      intro w hw hc
      have h1 : dRep l N U w φ = φ :=
        Subtype.ext (hn w ⟨hw, KStar.TotallyRealRoots.princ_anti (le_max_left n r) hc⟩)
      have h2 : cycZ k Ω l w ^ (-e) ∈ KStar.TotallyRealRoots.princ l r :=
        Subgroup.zpow_mem _ (KStar.TotallyRealRoots.princ_anti (le_max_right n r) hc) _
      rw [KStar.TotallyRealRoots.mem_princ] at h2
      obtain ⟨c, hc'⟩ := h2
      rw [dTw_apply, LinearMap.smul_apply, h1, sub_eq_iff_eq_add.1 hc', add_smul, one_smul, mul_comm, mul_smul, hr,
        smul_zero, zero_add]
    have hz : ∀ j : ℤ, dTw l N U e (γ ^ j) φ = φ := by
      intro j
      let S : Subgroup (G k Ω) :=
        { carrier := {g | dTw l N U e g φ = φ}
          mul_mem' := fun {a b} ha hb => by
            show dTw l N U e (a * b) φ = φ
            rw [map_mul, Module.End.mul_apply, show dTw l N U e b φ = φ from hb]; exact ha
          one_mem' := by
            show dTw l N U e 1 φ = φ
            rw [map_one]; rfl
          inv_mem' := fun {a} ha => by
            show dTw l N U e a⁻¹ φ = φ
            conv_lhs => rw [← show dTw l N U e a φ = φ from ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
      exact S.zpow_mem (show γ ∈ S from hφ) j
    have hcl : cycZ k Ω l v ∈ closure ((Subgroup.zpowers (cycZ k Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
      hγ.2 ⟨v, hv, rfl⟩
    have hop : IsOpen ((fun x : ℤ_[l]ˣ => x⁻¹ * cycZ k Ω l v) ⁻¹' (KStar.TotallyRealRoots.princ l (max n r) : Set ℤ_[l]ˣ)) :=
      (KStar.TotallyRealRoots.isOpen_princ _).preimage (by fun_prop)
    obtain ⟨x, hx, j, rfl⟩ := mem_closure_iff.1 hcl _ hop (by simp [one_mem])
    have h3 := hlev ((γ ^ j)⁻¹ * v) (U.mul_mem (U.inv_mem (U.zpow_mem (hVU hγ.1) j)) (hVU hv))
      (by rw [map_mul, map_inv, map_zpow]; exact hx)
    have h4 : v = γ ^ j * ((γ ^ j)⁻¹ * v) := by group
    rw [h4, map_mul, Module.End.mul_apply, h3, hz]
  constructor
  · ext φ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
    exact ⟨fun h => h ⟨γ, hγ.1⟩, fun h v => key φ h v.1 v.2⟩
  · ext φ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
    refine ⟨fun h => h ⟨γ⁻¹, V.inv_mem hγ.1⟩, fun h v => key φ ?_ v.1 v.2⟩
    conv_lhs => rw [← h]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
