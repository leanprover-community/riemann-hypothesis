import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinJacAsm
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocMassTyp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocJacOrd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PhiBijective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLocJacHypLemmas

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

variable {D : D7} (X : HidaSetting D)

theorem sig_ne_id : X.B.I.cm.sig ≠ AlgHom.id X.B.I.F X.B.I.E := by
  intro h
  have hall : ∀ a : X.B.I.E, a ∈ (⊥ : Subalgebra X.B.I.F X.B.I.E) := by
    intro a
    have h1 : X.B.I.cm.sig a = a := by rw [h]; rfl
    obtain ⟨c, hc⟩ := (X.B.I.cm.fixed a).1 h1
    exact Algebra.mem_bot.2 ⟨c, hc⟩
  have htop : (⊥ : Subalgebra X.B.I.F X.B.I.E) = ⊤ := eq_top_iff.2 fun a _ => hall a
  have h1 : Module.finrank X.B.I.F X.B.I.E = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
  have h2 := X.B.I.cm.deg2
  omega





end Formalism.L2.SG.Pf.MassDataX
