import { Store } from '../src/store.js';

let assert = chai.assert;

describe('store', function () {
  describe('create', function () {
    it('should assign incremental ids to new suspensions', function () {
      let store = new Store(1);
      let susp1 = store.create(0, []);
      let susp2 = store.create(0, []);
      assert.equal(susp2.id - susp1.id, 1);
    });

    it('should create alive suspensions', function () {
      let store = new Store(1);
      let susp = store.create(0, []);
      assert.isOk(susp.alive);
    });
  });

  describe('lookup', function () {
    it('should find a stored suspension', function () {
      let store = new Store(1);
      let susp = store.create(0, []);
      store.store(susp);
      let stored = store.lookup(0);
      assert.isOk(stored.has(susp));
    });

    it('should not find a non-stored suspension', function () {
      let store = new Store(1);
      let susp = store.create(0, []);
      let stored = store.lookup(0);
      assert.isNotOk(stored.has(susp));
    });

    it('should not find a killed suspension', function () {
      let store = new Store(1);
      let susp = store.create(0, []);
      store.store(susp);
      store.kill(susp);
      let stored = store.lookup(0);
      assert.isNotOk(stored.has(susp));
    });

    it('should return all the stored suspensions', function () {
      let store = new Store(1);
      let susp1 = store.create(0, []);
      let susp2 = store.create(0, []);
      let susp3 = store.create(0, []);
      store.store(susp1);
      store.store(susp2);
      store.store(susp3);
      let stored = store.lookup(0);
      assert.equal(stored.size, 3);
    });

    it('should provide an iterator that is robust under addition', function () {
      let store = new Store(1);
      let susp1 = store.create(0, []);
      let susp2 = store.create(0, []);
      store.store(susp1);
      let iter = store.lookup(0)[Symbol.iterator]();
      let r1 = iter.next();
      store.store(susp2);
      let r2 = iter.next();
      assert.equal(r2.value, susp2);
    });

    it('should provide an iterator that is robust under deletion', function () {
      let store = new Store(1);
      let susp1 = store.create(0, []);
      let susp2 = store.create(0, []);
      store.store(susp1);
      store.store(susp2);
      let iter = store.lookup(0)[Symbol.iterator]();
      let r1 = iter.next();
      store.kill(susp2);
      let r2 = iter.next();
      assert.isOk(r2.done);
      assert.equal(r2.value, undefined);
    });
  });

  describe('notInHistory', function () {
    it('should be true for an empty history', function () {
      let store = new Store(1);
      let susp = store.create(0, []);
      assert.isOk(store.notInHistory(1, [susp]));
    });

    it('should be false for a rule that has been added to history', function () {
      let store = new Store(1);
      let susp = store.create(0, []);
      store.addToHistory(1, [susp]);
      assert.isNotOk(store.notInHistory(1, [susp]));
    });
  });
});
