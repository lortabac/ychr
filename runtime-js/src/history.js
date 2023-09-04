export class HistoryItem {
  constructor(rule, suspensions) {
    this.rule = rule;
    this.suspensions = suspensions;
  }

  equals(other) {
    if(this.rule !== other.rule) {
      return false;
    }

    let length = this.suspensions.length;

    if(length !== other.suspensions.length) {
      return false;
    }

    for(let i = 0; i < length; i++) {
      if(this.suspensions[i] !== other.suspensions[i]) {
        return false;
      }
    }

    return true;
  }

  hashCode() {
    return rule + this.suspensions.reduce((acc, s) => {
      return acc + s.id;
    }, 0);
  }
}
