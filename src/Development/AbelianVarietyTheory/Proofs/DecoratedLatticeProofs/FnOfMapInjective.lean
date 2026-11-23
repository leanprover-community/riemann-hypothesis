module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.HermitianForms.LastCoordinateUniformizerVectorSpansOrthogonalLi
public import Formalism.LocalToGlobal.Columns.TiedValRat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.LocalToGlobal.Columns.TiedVal

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Core

theorem fnOf_map_injective {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (sh : ι → ℤ) (s : K →+* ℂ) {F F' : MvPolynomial (ι × Fin n × Fin n) K}
    (h : fnOf G sh 1 (MvPolynomial.map s F) = fnOf G sh 1 (MvPolynomial.map s F')) : F = F' :=
  MvPolynomial.map_injective s s.injective
    (Formalism.L2.Col.fnOf_injective G sh 1 (fun _ => by simp)
      (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}) h)

theorem exists_ptVal_at (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K) (x : (D.fm u).ptLat.V)
    (c : (D.fm u).clsP) : ∃ F : VV D.what₂.LL (sgT u),
      W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL F.1) := by
  obtain ⟨P, hP, hv⟩ := ((W.rat _).1 ⟨x, rfl⟩).2 c
  have e : Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) = Formalism.L2.Col.RatSpanG D.what₂.embLL (D.fm u).sg :=
    Formalism.L2.Col.RatSpanG_shW D.what₂.embLL (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
  have hP' : P ∈ Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) := by rw [e]; exact hP
  obtain ⟨F, hF, rfl⟩ := Formalism.L2.Col.exists_VV_of_mem_RatSpanG _ _ hP'
  exact ⟨⟨F, hF⟩, hv⟩

theorem exists_ptVal : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K), ∃ val : (D.fm u).ptLat.V →ₗ[D.what₂.LL] ((D.fm u).clsP → VV D.what₂.LL (sgT u)), (∀ x c, W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (val x c).1)) := by
  intro D u K W
  choose val hval using exists_ptVal_at D u K W
  refine ⟨{ toFun := val, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hval⟩
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    rw [← hval, Pi.add_apply, Submodule.coe_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ← hval, ← hval, Pi.add_apply]
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    have e : MvPolynomial.map D.what₂.embLL (a • (val x c).1) =
        D.what₂.embLL a • MvPolynomial.map D.what₂.embLL (val x c).1 := by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    rw [← hval, RingHom.id_apply, Pi.smul_apply, Submodule.coe_smul, e, LinearMap.map_smul, ← hval,
      LinearMap.map_smulₛₗ, LinearEquiv.map_smul, Pi.smul_apply]

end GlobalTheory.Core
