import { Var, isVar, isGround, getType, TVar, TNumber } from '../src/term.js';

let assert = chai.assert;

describe('term', function () {
  describe('isVar', function () {
    it('should be true for vars', function () {
      let v = new Var(0);
      assert.isOk(isVar(v));
    });

    it('should be false for numbers', function () {
      assert.isNotOk(isVar(1));
    });
  });

  describe('isGround', function () {
    it('should be false for vars', function () {
      let v = new Var(0);
      assert.isNotOk(isGround(v));
    });

    it('should be true for numbers', function () {
      assert.isOk(isGround(1));
    });
  });

  describe('getType', function () {
    it('should find the type of a var', function () {
      let v = new Var(0);
      assert.equal(getType(v), TVar);
    });

    it('should find the type of a number', function () {
      assert.equal(getType(1), TNumber);
    });
  });
});
