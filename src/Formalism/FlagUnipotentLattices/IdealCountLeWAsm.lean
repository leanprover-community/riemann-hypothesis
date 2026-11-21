import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ColonCountWeighted

namespace Formalism.HermitianLatticeCounting.Final.S6

theorem dualIndex : Formalism.HermitianLatticeCounting.S6.DualIndex := Formalism.HermitianLatticeCounting.P.dual_lattice_index
theorem subGen : Formalism.HermitianLatticeCounting.S6.SubGen := Formalism.HermitianLatticeCounting.P.submodule_generator_count
theorem extGen : Formalism.HermitianLatticeCounting.S6.ExtGen := Formalism.HermitianLatticeCounting.P.extension_generator_count
theorem cCount : Formalism.HermitianLatticeCounting.S6.CCount := Formalism.HermitianLatticeCounting.P.colon_count_bound
theorem quotCard : Formalism.HermitianLatticeCounting.S6.QuotCard := Formalism.HermitianLatticeCounting.P.height_loss_bound
theorem hLoss : Formalism.HermitianLatticeCounting.S6.HLoss := Formalism.HermitianLatticeCounting.P.loss_bound_holds

end Formalism.HermitianLatticeCounting.Final.S6
