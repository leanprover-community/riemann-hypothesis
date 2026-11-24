module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
public import Mathlib.Algebra.Algebra.ZMod

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem module_finite_z1_padicInt (l : ℕ) [Fact l.Prime] {k G : Type} [Field k] [Finite k] [CharP k l] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ ψ : G →* kˣ) (hΦ : PhiCond (Γ := G) l)
    (hχ : IsOpen (χ.ker : Set G)) (hψ : IsOpen (ψ.ker : Set G)) : Finite (Z1 χ ψ) := by
  classical
  letI := ZMod.algebra k l
  haveI : Module.Finite (ZMod l) k := Module.Finite.of_finite
  let N : Subgroup G := χ.ker ⊓ ψ.ker
  have hNo : IsOpen (N : Set G) := by
    show IsOpen ((χ.ker ⊓ ψ.ker : Subgroup G) : Set G)
    rw [Subgroup.coe_inf]
    exact hχ.inter hψ
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  haveI := hΦ N hNo
  let b := Module.finBasis (ZMod l) k
  have mem : ∀ a ∈ Z1 χ ψ, IsLocallyConstant a ∧
      ∀ g h : G, a (g * h) = (χ g : k) * a h + a g * (ψ h : k) := fun a ha => ha
  have hadd : ∀ a ∈ Z1 χ ψ, ∀ x y : N, a ((x : G) * (y : G)) = a x + a y := by
    intro a ha x y
    have hx : χ (x : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).1
    have hy : ψ (y : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp y.2).2
    rw [(mem a ha).2, hx, hy]
    simp [add_comm]
  let φ : ∀ a ∈ Z1 χ ψ, Fin (Module.finrank (ZMod l) k) → (N →* Multiplicative (ZMod l)) :=
    fun a ha i => MonoidHom.mk' (fun x => Multiplicative.ofAdd (b.repr (a x) i)) (by
      intro x y
      simp [hadd a ha x y, ofAdd_add])
  have hφo : ∀ a (ha : a ∈ Z1 χ ψ) i, IsOpen ((φ a ha i).ker : Set N) := by
    intro a ha i
    have hlc : IsLocallyConstant (fun x : N => b.repr (a x) i) :=
      ((mem a ha).1.comp_continuous continuous_subtype_val).comp (fun y => b.repr y i)
    have e : ((φ a ha i).ker : Set N) = {x | (fun x : N => b.repr (a x) i) x = 0} := by
      ext x
      simp [φ, MonoidHom.mem_ker]
    rw [e]
    exact hlc.isOpen_fiber 0
  let F : Z1 χ ψ → (G ⧸ N → k) ×
      (Fin (Module.finrank (ZMod l) k) → {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}) :=
    fun a => (fun q => (a : G → k) q.out, fun i => ⟨φ a a.2 i, hφo a a.2 i⟩)
  refine Finite.of_injective F ?_
  rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hN' : ∀ x : N, a x = a' x := by
    intro x
    apply b.repr.injective
    ext i
    exact congrArg (fun f => Multiplicative.toAdd ((f i).1 x)) h2
  apply Subtype.ext
  funext g
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
  have e1 : a (QuotientGroup.mk g : G ⧸ N).out = a' (QuotientGroup.mk g : G ⧸ N).out := congrFun h1 _
  have hg : g = (QuotientGroup.mk g : G ⧸ N).out * ((n⁻¹ : N) : G) := by
    rw [hn]; simp [mul_assoc]
  show a g = a' g
  rw [hg, (mem a ha).2, (mem a' ha').2, hN' n⁻¹, e1]

theorem UpperTheory.V.CA.exists_multFree_of_phiCond_of_injective_chars :
    ∀ (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ), PhiCond (Γ := G) l → (∀ i, IsOpen ((χ i).ker : Set G)) → Function.Injective χ → ∃ h, MultFree χ h := by
  intro l _ n k G _ _ _ _ _ _ _ _ χ hΦ hopen hinj
  refine ⟨∑ i, ∑ j, Module.finrank k (Z1 (χ i) (χ j)), hopen, hinj, fun i j _ => ?_⟩
  haveI := module_finite_z1_padicInt l (χ i) (χ j) hΦ (hopen i) (hopen j)
  refine ⟨inferInstance, ?_⟩
  calc Module.finrank k (Z1 (χ i) (χ j)) ≤ ∑ j', Module.finrank k (Z1 (χ i) (χ j')) :=
        Finset.single_le_sum (f := fun j' => Module.finrank k (Z1 (χ i) (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Module.finrank k (Z1 (χ i') (χ j')) :=
        Finset.single_le_sum (f := fun i' => ∑ j', Module.finrank k (Z1 (χ i') (χ j')))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
