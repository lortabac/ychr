import { Logic } from '../src/logic.js';

let assert = chai.assert;

describe('logic', function () {
  describe('unify', function () {
    it('should succeed on two equal numbers', function () {
      let logic = new Logic();
      assert.isOk(logic.unify(1, 1));
    });

    it('should fail on two unequal numbers', function () {
      let logic = new Logic();
      assert.isNotOk(logic.unify(1, 2));
    });

    it('should succeed on two vars', function () {
      let logic = new Logic();
      let var0 = logic.newVar(0);
      let var1 = logic.newVar(1);
      assert.isOk(logic.unify(var0, var1));
    });

    it('should succeed on var and number', function () {
      let logic = new Logic();
      let var0 = logic.newVar(0);
      assert.isOk(logic.unify(var0, 1));
    });

    it('should succeed on number and var', function () {
      let logic = new Logic();
      let var1 = logic.newVar(0);
      assert.isOk(logic.unify(1, var1));
    });
  });

  describe('applyBindings', function () {
    it('should not transform numbers', function () {
      let logic = new Logic();
      assert.equal(logic.applyBindings(1), 1);
    });

    it('should transform vars to numbers', function () {
      let logic = new Logic();
      let v = logic.newVar(0);
      logic.unify(v, 1);
      assert.equal(logic.applyBindings(v), 1);
    });

    it('should transform aliased vars to numbers', function () {
      let logic = new Logic();
      let var0 = logic.newVar(0);
      let var1 = logic.newVar(1);
      logic.unify(var0, var1);
      logic.unify(var1, 1);
      assert.equal(logic.applyBindings(var0), 1);
    });

    it('should handle recursive aliasing', function () {
      let logic = new Logic();
      let var0 = logic.newVar(0);
      let var1 = logic.newVar(1);
      logic.unify(var0, var1);
      logic.unify(var1, var0);
      logic.unify(var1, 1);
      assert.equal(logic.applyBindings(var0), 1);
    });
  });
});
