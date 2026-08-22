/** @type {import('ts-jest').JestConfigWithTsJest} */
module.exports = {
  preset: 'ts-jest',
  testEnvironment: 'node',
  testTimeout: 1_200_000,
  roots: ['<rootDir>/test/pic'],
  testMatch: ['**/*.test.ts'],
  transform: {
    '^.+\\.[jt]s$': ['ts-jest', {
      tsconfig: 'tsconfig.json',
    }],
  },
  transformIgnorePatterns: [
    'node_modules/',
  ],
};
