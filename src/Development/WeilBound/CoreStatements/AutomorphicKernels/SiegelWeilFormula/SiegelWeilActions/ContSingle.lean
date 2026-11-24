module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainLe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CBDM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsSigmaNe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PiMapConst
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.WMUnitary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContSingle

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ptEx' (d : SD σ) {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {X : Type} [TopologicalSpace X] (M M' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Continuous M) (hM' : Continuous M') (h : ∀ c, M c * M' c = 1)
    (hu : ∀ c, (M c)ᵀ * kunf.jw d.n (((ε : ℤ) : AE F E)) * (M c).map (cA σ) = kunf.jw d.n (((ε : ℤ) : AE F E))) :
    ∃ f : X → d.G, Continuous f ∧ ∀ c, inFrame d.b (f c) = M c := by
  have hone : incM F (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hPQ : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.mul_inv, hone]
  have hQP : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.inv_mul, hone]
  have hM'M : ∀ c, M' c * M c = 1 := fun c => by
    first
    | exact mul_eq_one_comm.mp (h c)
  let N : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M c * incM F (d.b⁻¹).1
  let N' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M' c * incM F (d.b⁻¹).1
  have hNN' : ∀ c, N c * N' c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M c) (M' c), h c, Matrix.one_mul, hPQ]
  have hN'N : ∀ c, N' c * N c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M' c) (M c), hM'M c, Matrix.one_mul, hPQ]
  let u : X → GL (Fin d.n ⊕ Fin d.n) (AE F E) := fun c => ⟨N c, N' c, hNN' c, hN'N c⟩
  have mem : ∀ c, u c ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    intro c
    obtain ⟨x, hx⟩ := PositivityTheory.SiegelWeilFormula.kunf.exists_of_frame hε (M c) (M' c) (h c) (hu c)
    have hx' : x.1.1 = N c := by
      show x.1.1 = incM F d.b.1 * M c * incM F (d.b⁻¹).1
      rw [← hx]
      show x.1.1 = incM F d.b.1 * (incM F (d.b⁻¹).1 * x.1.1 * incM F d.b.1) * incM F (d.b⁻¹).1
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    have e : u c = x.1 := Units.ext hx'.symm
    rw [e]
    exact x.2
  refine ⟨fun c => ⟨u c, mem c⟩, ?_, ?_⟩
  · apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact (continuous_const.matrix_mul hM).matrix_mul continuous_const
    · exact (continuous_const.matrix_mul hM').matrix_mul continuous_const
  · intro c
    show incM F (d.b⁻¹).1 * N c * incM F d.b.1 = M c
    simp only [N, Matrix.mul_assoc]
    rw [hQP, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContSingle =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContSingle", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainLe\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CBDM\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsSigmaNe\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PiMapConst\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.WMUnitary\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame\nimport Formalism.LocalToGlobal.IndefiniteReal.PHeisFC\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

def CLawEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d),
  ∃ (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G) (κ : Measure ((Fin L.n → AE F E) × AF F)),
    CLaw R L w₁ cM κ ∧ w₁ ∈ rat2 σ d.Y ∧
    (∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)) ∧
    Continuous cM ∧ κ.IsAddHaarMeasure ∧
    ∃ δ : E, δ ≠ 0 ∧ ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (c.1 j))
      (Matrix.single L.i₀ L.i₀ (c.2 • inclR (F := F) (AF F) δ)) 0 A'

theorem cont_single {X α : Type} [TopologicalSpace X] [TopologicalSpace α] [Zero α] {m p : Type} [DecidableEq m]
    [DecidableEq p] (i : m) (j : p) {f : X → α} (hf : Continuous f) : Continuous fun x => Matrix.single i j (f x) :=
  continuous_pi fun a => continuous_pi fun b => by
    simp only [Matrix.single_apply]
    split_ifs
    exacts [hf, continuous_const]

theorem cLawEx : CLawEx := by
  intro F E _ _ _ _ _ σ d R L
  have hε := R.hε
  have hem : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  set e : AE F E := ((R.ε : ℤ) : AE F E) with he_def
  have hee : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  obtain ⟨δ, hδ0, hδ⟩ := CL.deltaEx' d.cm R.ε
  obtain ⟨κ, hκ, hsc⟩ := CL.measEx' (F := F) (E := E) L.n d.bs

  let M₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ (1 : E) ((R.ε : ℤ) : E)
  let M₀' : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ ((R.ε : ℤ) : E) (1 : E)
  have hW : incM F M₀ = CL.wM L.i₀ (1 : AE F E) e := by
    show M₀.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hW' : incM F M₀' = CL.wM L.i₀ e (1 : AE F E) := by
    show M₀'.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hWW : incM F M₀ * incM F M₀' = 1 := by
    rw [hW, hW']; exact CL.wM_mul L.i₀ _ _ _ _ (one_mul 1) hee
  have hWu : (incM F M₀)ᵀ * kunf.jw d.n e * (incM F M₀).map (cA σ) = kunf.jw d.n e := by
    rw [hW]
    refine CL.wM_unitary L.i₀ (cA σ).toRingHom 1 e e ?_ ?_
    · simp only [AlgHom.toRingHom_eq_coe, map_one, mul_one, hee]
    · simp only [AlgHom.toRingHom_eq_coe, he_def, map_intCast, one_mul]
  obtain ⟨w₁, hw₁⟩ := kunf.exists_of_frame hε (incM F M₀) (incM F M₀') hWW hWu
  have hw₁' : inFrame d.b w₁ = CL.wM L.i₀ (1 : AE F E) e := hw₁.trans hW

  set δ' : AE F E := inclR (F := F) (AF F) δ with hδ'
  let Mc : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em c.1 (fun j => cA σ (c.1 j)) (c.2 • δ')
  let Mc' : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em (-c.1) (-fun j => cA σ (c.1 j)) (-(c.2 • δ'))
  have hcont : ∀ s : AF F → AF F, Continuous s → ∀ t : (Fin L.n → AE F E) → (Fin L.n → AE F E), Continuous t →
      Continuous fun c : (Fin L.n → AE F E) × AF F =>
        CL.cB L.i₀ L.em (t c.1) (fun j => cA σ (t c.1 j)) (s c.2 • δ') := by
    intro s hs t ht
    refine Continuous.matrix_fromBlocks ?_ ?_ continuous_const ?_
    · exact continuous_const.add (continuous_finsetSum _ fun j _ =>
        cont_single _ _ ((continuous_apply j).comp (ht.comp continuous_fst)))
    · exact cont_single _ _ (Continuous.smul (f := fun c : (Fin L.n → AE F E) × AF F => s c.2) (g := fun _ => δ')
        (hs.comp continuous_snd) continuous_const)
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => cont_single _ _
        ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp ((continuous_apply j).comp (ht.comp continuous_fst))))
  have hMc : Continuous Mc := hcont id continuous_id id continuous_id
  have hMc' : Continuous Mc' := by
    have := hcont (fun a => -a) continuous_neg (fun u => -u) continuous_neg
    convert this using 2 with c
    simp only [Mc', neg_smul, Pi.neg_apply, map_neg]
    rfl
  have cA_inclR (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have cA_invol (z : AE F E) : cA σ (cA σ z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
        (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, _root_.GlobalTheory.AdelicU.cm_conj_conj d.cm]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcA_z : ∀ a : AF F, cA σ (a • δ') = -(e * (a • δ')) := by
    intro a
    rw [map_smul, hδ', cA_inclR δ, hδ, map_neg, map_mul, map_intCast, smul_neg, mul_smul_comm]
  obtain ⟨cM, hcMc, hcM⟩ := CL.ptEx' d hε Mc Mc' hMc hMc'
    (fun c => CL.cB_mul hem c.1 _ _) (fun c => CL.cB_unitary hem (cA σ).toRingHom
      cA_invol e hee c.1 (c.2 • δ') (hcA_z c.2))
  have hfr := fun x y => GlobalTheory.EisBL.DoubledParabolic.inFrame_mul (σ := σ) (Y := d.Y) d.b x y
  refine ⟨w₁, cM, κ, ⟨?_, ?_, ?_⟩, kunf.rat_of_inFrame hw₁, ⟨1, (R.ε : ℤ), one_ne_zero, ?_, ?_⟩, hcMc, hκ,
    ⟨δ, hδ0, fun c => ⟨_, hcM c⟩⟩⟩
  ·
    intro w τ y g hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := CL.rEx d w
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, CL.frame_dil d R w r hrw hro hrf L.i₀ hy]
    exact CL.comm_dM L.i₀ _ (L.j_out g) _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := CL.rEx d w
    have hy' := CL.isDil_inv hy
    obtain ⟨t, ht, ha, hχ⟩ := CL.par_dil d R w L.i₀ hy'
    refine ⟨R.ι w y⁻¹, t, ht, by rw [ha]; ring_nf, hχ, ?_⟩
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, hw₁', CL.frame_dil d R w r hrw hro hrf L.i₀ hy, CL.frame_dil d R w r hrw hro hrf L.i₀ hy', neg_neg]
    exact CL.wM_dM L.i₀ _ _ _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, hrm, hrw, hro, hrf⟩ := CL.rEx d w
    obtain ⟨sc, hsc1, hsc2⟩ := hsc (r (-τ))
    refine ⟨sc, fun c => ?_, ?_⟩
    · apply kunf.inFrame_injective d.b
      rw [hfr, hfr, hcM, hcM, CL.frame_dil d R w r hrw hro hrf L.i₀ hy]
      have hxy : ((r τ : AF F) • (1 : AE F E)) * ((r (-τ) : AF F) • (1 : AE F E)) = 1 := by
        rw [smul_mul_smul_comm, one_mul, ← Units.val_mul, ← hr0, add_neg_cancel, hr1]; simp
      rw [CL.cB_dM hem _ _ _ _ _ hxy, hsc1]
      congr 1
      simp only [Mc]
      congr 1
      · funext j; exact smul_one_mul _ _
      · funext j; rw [map_smul, smul_one_mul]
      · rw [mul_assoc, smul_one_mul, smul_one_mul, smul_assoc, mul_smul]
    · rw [hsc2, hrm, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul, ← Atop.LD.n_succ L]
      congr 2
      push_cast; ring
  · simp
  · rw [hw₁']; simp [CL.wM, map_intCast, map_one, he_def]

end PositivityTheory.SiegelWeilFormula.Act

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContSingle =====
