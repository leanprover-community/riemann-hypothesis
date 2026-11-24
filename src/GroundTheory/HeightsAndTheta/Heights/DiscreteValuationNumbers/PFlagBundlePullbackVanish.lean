module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundle
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundlePullbackVanish

theorem liftDeg_eq_pullDeg {K : Type*} (L : K → ℤ) :
    liftDeg L = FieldNumbers.pullDeg Function.Embedding.some L := by
  funext o
  cases o with
  | none =>
    rw [FieldNumbers.pullDeg, Function.extend_apply' _ _ _ (by simp)]
    rfl
  | some k =>
    exact (Function.Embedding.some.injective.extend_apply L 0 k).symm

theorem contract_projIdeal {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
    {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) {N M : ℕ} {E : Type} [AddCommGroup E]
    [Module Ω E] (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    {Φ : Type} [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ) :
    FieldNumbers.contractPrime Function.Embedding.some (projIdeal F y w φ t) =
      pointIdeal (ι := fun k => bundleIdx ι M (Function.Embedding.some k)) F y := by
  let ψ : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename Option.some).toRingHom.comp (MvPolynomial.map (algebraMap Ω Φ))
  have hψ : Function.Injective ψ :=
    (rename_injective _ (Option.some_injective K)).comp
      (map_injective _ (algebraMap Ω Φ).injective)
  ext x
  simp only [FieldNumbers.contractPrime, projIdeal, pointIdeal, Ideal.mem_comap, RingHom.mem_ker]
  refine Iff.trans ?_ (map_eq_zero_iff ψ hψ)
  refine Iff.of_eq (congrArg (· = 0) ?_)
  induction x using MvPolynomial.induction_on with
  | C r =>
    simp [ψ, pointConeMap, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X, eval₂Hom_X', pointConeMap, aeval_X]
    simp [ψ, FieldNumbers.blockIncl, projCoord]
    exact Or.inl rfl

theorem proof (hPF : FieldNumbers.ProjectionFormulaContracted.Statement.{0})
    (hDim : FlagBundleDim.Statement) : FlagBundlePullbackVanish.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hVdim N E _ _ B w b hflag M a φ hφ Φ _ _ t ht i hi2 hiN L hL
  obtain ⟨hP, hrel⟩ := hDim F Ω K ι y e hV hVdim N E B w b hflag M a φ hφ Φ t ht i (by omega) hiN
  have hlen : (L.map liftDeg).length = e + i - 1 := by simp; omega
  have hrel' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t i)) =
      (((L.map liftDeg).length : ℕ) : WithBot (WithTop ℤ)) := by rw [hrel, hlen]
  have hrelV : FieldNumbers.relDim (ι := ι) (pointIdeal F y) =
      (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim, hVdim]
    have : (((e + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = e := by push_cast; ring
    exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
  have hcontr : FieldNumbers.relDim
      (FieldNumbers.contractPrime Function.Embedding.some (projIdeal F y w φ (truncCoord t i))) <
      (((L.map liftDeg).length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [contract_projIdeal]
    show FieldNumbers.relDim (ι := ι) (pointIdeal F y) < _
    rw [hrelV, hlen]
    show (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) <
      ((((e + i - 1 : ℕ) : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))
  have hzero := hPF F K (Option K) Function.Embedding.some (bundleIdx ι M)
    (projIdeal F y w φ (truncCoord t i)) hP _ hrel' hcontr
    (fun k => L.get (Fin.cast (by simp) k))
  rw [intNumL, ← hzero]
  congr 1
  funext k
  simp [liftDeg_eq_pullDeg]

end FlagBundlePullbackVanish

end

end GroundTheory.Heights₂.Heights.NumbersDVR
