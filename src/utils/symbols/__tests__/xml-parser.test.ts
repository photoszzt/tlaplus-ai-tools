import { parseXmlSymbols } from '../xml-parser';

describe('xml-parser', () => {
  describe('parseXmlSymbols', () => {
    it('parses empty modules element', () => {
      const xml = '<modules></modules>';
      const result = parseXmlSymbols(xml);
      expect(result).toEqual([]);
    });

    it('parses UserDefinedOpKind entries', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Init</uniquename>
        <location>
          <filename>Counter</filename>
          <line><begin>10</begin><end>10</end></line>
          <column><begin>1</begin><end>15</end></column>
        </location>
        <level>1</level>
        <arity>0</arity>
        <pre-comments>Initial state predicate</pre-comments>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result).toHaveLength(1);
      expect(result[0].name).toBe('Init');
      expect(result[0].module).toBe('Counter');
      expect(result[0].uniqueName).toBe('Counter!Init');
      expect(result[0].level).toBe(1);
      expect(result[0].arity).toBe(0);
      expect(result[0].rawKind).toBe('UserDefinedOpKind');
      expect(result[0].comment).toBe('Initial state predicate');
      expect(result[0].location).toEqual({
        file: 'Counter',
        start: { line: 10, col: 1 },
        end: { line: 10, col: 15 }
      });
    });

    it('parses OpDeclNode entries (variables/constants)', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <OpDeclNode>
        <uniquename>Counter!count</uniquename>
        <location>
          <filename>Counter</filename>
          <line><begin>5</begin><end>5</end></line>
          <column><begin>1</begin><end>5</end></column>
        </location>
        <level>1</level>
        <arity>0</arity>
      </OpDeclNode>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result).toHaveLength(1);
      expect(result[0].name).toBe('count');
      expect(result[0].module).toBe('Counter');
      expect(result[0].level).toBe(1);
      expect(result[0].rawKind).toBe('OpDeclNode');
    });

    it('parses constant declarations (level 0)', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <OpDeclNode>
        <uniquename>Counter!MaxValue</uniquename>
        <location>
          <filename>Counter</filename>
          <line><begin>3</begin><end>3</end></line>
          <column><begin>1</begin><end>8</end></column>
        </location>
        <level>0</level>
        <arity>0</arity>
      </OpDeclNode>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result).toHaveLength(1);
      expect(result[0].name).toBe('MaxValue');
      expect(result[0].level).toBe(0);
    });

    it('parses TheoremDefNode entries', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <TheoremDefNode>
        <uniquename>Counter!TypeOK</uniquename>
        <location>
          <filename>Counter</filename>
          <line><begin>20</begin><end>22</end></line>
          <column><begin>1</begin><end>1</end></column>
        </location>
      </TheoremDefNode>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result).toHaveLength(1);
      expect(result[0].name).toBe('TypeOK');
      expect(result[0].rawKind).toBe('TheoremDefNode');
    });

    it('parses AssumeDef entries', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <AssumeDef>
        <uniquename>Counter!Assumption1</uniquename>
        <location>
          <filename>Counter</filename>
          <line><begin>25</begin><end>25</end></line>
          <column><begin>1</begin><end>20</end></column>
        </location>
      </AssumeDef>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result).toHaveLength(1);
      expect(result[0].name).toBe('Assumption1');
      expect(result[0].rawKind).toBe('AssumeDef');
    });

    it('parses multiple entries', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <OpDeclNode>
        <uniquename>Counter!MaxValue</uniquename>
        <location><filename>Counter</filename><line><begin>3</begin><end>3</end></line><column><begin>1</begin><end>8</end></column></location>
        <level>0</level>
        <arity>0</arity>
      </OpDeclNode>
    </entry>
    <entry>
      <OpDeclNode>
        <uniquename>Counter!count</uniquename>
        <location><filename>Counter</filename><line><begin>5</begin><end>5</end></line><column><begin>1</begin><end>5</end></column></location>
        <level>1</level>
        <arity>0</arity>
      </OpDeclNode>
    </entry>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Init</uniquename>
        <location><filename>Counter</filename><line><begin>10</begin><end>10</end></line><column><begin>1</begin><end>15</end></column></location>
        <level>1</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result).toHaveLength(3);
      expect(result.map(s => s.name)).toEqual(['MaxValue', 'count', 'Init']);
    });

    it('extracts module name from uniquename with ! separator', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <UserDefinedOpKind>
        <uniquename>MyModule!MyOperator</uniquename>
        <location><filename>MyModule</filename><line><begin>1</begin><end>1</end></line><column><begin>1</begin><end>1</end></column></location>
        <level>1</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result[0].module).toBe('MyModule');
      expect(result[0].name).toBe('MyOperator');
    });

    it('handles missing optional fields gracefully', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Op</uniquename>
        <location><filename>Counter</filename><line><begin>1</begin><end>1</end></line><column><begin>1</begin><end>1</end></column></location>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result).toHaveLength(1);
      expect(result[0].level).toBeUndefined();
      expect(result[0].arity).toBeUndefined();
      expect(result[0].comment).toBeUndefined();
    });

    it('returns empty array on malformed XML without modules', () => {
      const xml = '<modules><unclosed>';
      const result = parseXmlSymbols(xml);
      expect(result).toEqual([]);
    });

    it('handles action-level operators (level 2)', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Next</uniquename>
        <location><filename>Counter</filename><line><begin>15</begin><end>18</end></line><column><begin>1</begin><end>1</end></column></location>
        <level>2</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result[0].level).toBe(2);
    });

    it('handles temporal-level operators (level 3)', () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Spec</uniquename>
        <location><filename>Counter</filename><line><begin>20</begin><end>20</end></line><column><begin>1</begin><end>30</end></column></location>
        <level>3</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;

      const result = parseXmlSymbols(xml);

      expect(result[0].level).toBe(3);
    });
  });
});
