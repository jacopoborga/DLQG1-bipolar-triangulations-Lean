"""Bounded negative controls for the exact comparator Challenge-hole exception."""
import copy,hashlib,json,sys,unittest
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'scripts'))
from check_release import ROOT,check_challenge_config,check_challenge_text,check_proof_tokens,load_challenges
BASE='module\nnamespace Test\ntheorem result : True := by\n  sorry\nend Test\n'
class ChallengeHoles(unittest.TestCase):
 def test_compared_terminal_hole(self):check_proof_tokens('Challenge.lean',BASE,['Test.result'])
 def test_production_hole_rejected(self):
  with self.assertRaises(ValueError):check_proof_tokens('DirectedDistances/Example.lean',BASE)
 def test_solution_hole_rejected(self):
  with self.assertRaises(ValueError):check_proof_tokens('Palomar/Pilot/Solution.lean',BASE)
 def test_extra_tactic_before_hole_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('  sorry','  skip\n  sorry'),['Test.result'])
 def test_extra_tactic_after_hole_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('  sorry','  sorry\n  trivial'),['Test.result'])
 def test_noncompared_declaration_hole_rejected(self):
  text=BASE.replace('end Test','theorem extra : True := by sorry\nend Test')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
 def test_renamed_declaration_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE.replace('result :','different :'),['Test.result'])
 def test_nested_comment_is_masked(self):
  check_challenge_text(BASE.replace('  sorry','  /- sorry /- admit -/ -/ sorry'),['Test.result'])
 def test_admit_is_never_allowed(self):
  with self.assertRaises(ValueError):check_proof_tokens('Challenge.lean',BASE.replace('sorry','admit'),['Test.result'])
 def test_custom_axiom_is_never_allowed(self):
  with self.assertRaises(ValueError):check_proof_tokens('Challenge.lean',BASE+'axiom bad : False\n',['Test.result'])
 def test_hole_in_noncompared_definition_rejected(self):
  with self.assertRaises(ValueError):check_challenge_text(BASE+'def extra : True := by sorry\n',['Test.result'])
 def test_actual_exact_challenges_and_configurations(self):
  specs=load_challenges()
  base={'Palomar/Pilot/Challenge.lean','Palomar/AppendixA/Challenge.lean'}
  self.assertEqual(sum(len(specs[p]['declarations']) for p in base),7)
  self.assertTrue(all(s['declarations'] for s in specs.values()))
 def test_config_name_mismatch_rejected(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['theorem_names']=['Test.other']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_config_extra_kernel_key_rejected(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['external_kernels']=[]
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_config_nanoda_required(self):
  spec=next(iter(load_challenges().values()));config=json.loads((ROOT/spec['config']).read_text())
  config['enable_nanoda']=False
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_proved_public_typing_auxiliary_allowed(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.Example.record._proof_1']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  check_challenge_config(spec,config)
 def test_typing_auxiliary_is_not_an_extra_hole(self):
  with self.assertRaises(ValueError):
   check_challenge_text(BASE+'theorem DirectedDistances.Example.record._proof_1 : True := by sorry\n',['Test.result'])
 def test_arbitrary_auxiliary_name_rejected(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['Test.unreviewed']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_duplicate_proved_auxiliary_rejected(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  name='DirectedDistances.Example.record._proof_1'
  spec['proved_auxiliaries']=[name,name]
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_definition_holes_remain_forbidden_with_typing_auxiliary(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.Example.record._proof_1']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  config['definition_names']=['DirectedDistances.Example.data']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_typing_auxiliary_budget_enforced(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.Example.record._proof_'+str(i) for i in range(13)]
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_named_proved_characterization_allowed_only_in_finite_config(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['path']='Palomar/Principal/BoltzmannDistances/Challenge.lean'
  spec['declarations']=['DLQG1.Palomar.Principal.boltzmann_distances']
  spec['solution_path']='Palomar/Principal/BoltzmannDistances/Solution.lean'
  spec['proved_auxiliaries']=['DirectedDistances.PlanarMap.mem_sourceSinkPathLengthsBase']
  config['challenge_module']='Palomar.Principal.BoltzmannDistances.Challenge'
  config['solution_module']='Palomar.Principal.BoltzmannDistances.Solution'
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  check_challenge_config(spec,config)
 def test_named_proved_characterization_rejected_in_other_config(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.PlanarMap.mem_sourceSinkPathLengthsBase']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_actual_probability_theorem_allowed_only_for_cells(self):
  for module in ['CellLDP','CellSDP']:
   spec=copy.deepcopy(next(iter(load_challenges().values())))
   config=json.loads((ROOT/spec['config']).read_text())
   spec['path']='Palomar/Principal/'+module+'/Challenge.lean'
   spec['solution_path']='Palomar/Principal/'+module+'/Solution.lean'
   spec['declarations']=['DLQG1.Palomar.Principal.cell_ldp' if module=='CellLDP' else 'DLQG1.Palomar.Principal.cell_sdp']
   spec['proved_auxiliaries']=['DirectedDistances.RandomWalk.instIsProbabilityMeasureFinOfNatNatUniformCodeMeasure']
   config['challenge_module']='Palomar.Principal.'+module+'.Challenge'
   config['solution_module']='Palomar.Principal.'+module+'.Solution'
   config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
   check_challenge_config(spec,config)
 def test_actual_probability_theorem_rejected_for_unrelated_config(self):
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['proved_auxiliaries']=['DirectedDistances.RandomWalk.instIsProbabilityMeasureFinOfNatNatUniformCodeMeasure']
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def busemann_typing_fixture(self):
  from check_release import BUSEMANN_TYPING_AUXILIARIES
  spec=copy.deepcopy(next(iter(load_challenges().values())))
  config=json.loads((ROOT/spec['config']).read_text())
  spec['path']='Palomar/Principal/Busemann/Challenge.lean'
  spec['solution_path']='Palomar/Principal/Busemann/Solution.lean'
  spec['declarations']=['DLQG1.Palomar.Principal.busemann']
  spec['proved_auxiliaries']=sorted(BUSEMANN_TYPING_AUXILIARIES)
  config['challenge_module']='Palomar.Principal.Busemann.Challenge'
  config['solution_module']='Palomar.Principal.Busemann.Solution'
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  return spec,config
 def test_exact_busemann_thirteen_typing_certificates_allowed(self):
  spec,config=self.busemann_typing_fixture()
  check_challenge_config(spec,config)
 def test_busemann_thirteen_certificates_wrong_path_rejected(self):
  spec,config=self.busemann_typing_fixture()
  spec['path']='Palomar/Principal/CellLDP/Challenge.lean'
  spec['solution_path']='Palomar/Principal/CellLDP/Solution.lean'
  config['challenge_module']='Palomar.Principal.CellLDP.Challenge'
  config['solution_module']='Palomar.Principal.CellLDP.Solution'
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_busemann_thirteen_changed_certificate_set_rejected(self):
  spec,config=self.busemann_typing_fixture()
  spec['proved_auxiliaries'][-1]='DirectedDistances.Example.unreviewed._proof_999'
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_busemann_fourteen_typing_certificates_rejected(self):
  spec,config=self.busemann_typing_fixture()
  spec['proved_auxiliaries'].append('DirectedDistances.Example.unreviewed._proof_999')
  config['theorem_names']=spec['declarations']+spec['proved_auxiliaries']
  with self.assertRaises(ValueError):check_challenge_config(spec,config)
 def test_attributed_compared_theorem_hole_allowed(self):
  check_challenge_text(BASE.replace('theorem result','@[simp] theorem result'),['Test.result'])
 def test_attributed_definition_after_hole_is_new_command(self):
  text=BASE.replace('end Test','@[expose] noncomputable def next : Nat := 0\nend Test')
  check_challenge_text(text,['Test.result'])
 def test_tactic_after_hole_before_attributed_definition_rejected(self):
  text=BASE.replace('  sorry','  sorry\n  trivial').replace('end Test','@[expose] def next : Nat := 0\nend Test')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
 def test_attributed_unlisted_theorem_hole_rejected(self):
  text=BASE.replace('end Test','@[simp] theorem extra : True := by sorry\nend Test')
  with self.assertRaises(ValueError):check_challenge_text(text,['Test.result'])
if __name__=='__main__':unittest.main()
