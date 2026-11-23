module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColsSharpDictionary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumInnerClassRepsIndep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOneStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colDict_isometric_of_reps :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂) (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)), Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj := by
  intro D X u F Tr hK hsig hL hS what₂ cs hinj hreps T T'
  obtain ⟨hcls, hwt⟩ := GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hsig hL
  have hwt1 := hwt hS
  obtain ⟨hψ, hπ, heq, -, -⟩ := GlobalTheory.St.cols_sharp_dictionary D X u hK
  have key := GlobalTheory.sum_inner_classReps_indep (Gam X u) (Hinf X u) (Hfin X u) (iotaI X u) (iotaF X u)
    (Ku X u hK) (psiK X u hK) (X.Vpi u) (piRep X u) hπ hψ cs.Cl ((D.mem u).C.cls 0) cs.h Tr.hc hreps hcls
    (shP X u (toCu X hK T').1) (shP X u (toCu X hK T).1) (heq _) (heq _)
  have hsh : ∀ (S : Formalism.L2.SG.PackageTie2.ColT hinj) ρ, (Formalism.L2.SG.PackageTie2.shT hinj S).ofLp ρ = shP X u (toCu X hK S).1 (cs.h ρ) := fun S ρ => rfl
  show inner ℂ (Formalism.L2.SG.PackageTie2.shT hinj T') (Formalism.L2.SG.PackageTie2.shT hinj T) = _
  rw [PiLp.inner_apply]
  simp only [hsh]
  rw [key]
  have hd : ∀ (S : Formalism.L2.SG.PackageTie2.ColT hinj) c, colDictL X Tr hK (toCu X hK S) c = fun z => Tr.J (shP X u (toCu X hK S).1 (Tr.hc c)) (F.val0.eY z) := fun S c => rfl
  have hterm : ∀ c, (D.fm u).ipV 0 c (colDictL X Tr hK (toCu X hK T) c) (colDictL X Tr hK (toCu X hK T') c) = ⟪shP X u (toCu X hK T').1 (Tr.hc c), shP X u (toCu X hK T).1 (Tr.hc c)⟫_ℂ := by
    intro c
    rw [hd, hd]
    exact Tr.J_isom c _ _
  unfold Formalism.BasicNotions.MemberForms.ipC
  simp only [hwt1, one_mul, hterm]

end GlobalTheory.St

end
